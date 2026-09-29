-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
-- name    : AutomorphicForm.lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/90976c0b-b5f4-5272-b092-8dc074f1970b
-- title:
--   Section-weight swap in archimedean Iwasawa coordinates
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite, put $K_\infty = \mathrm{InfiniteAdeleRing}\,K$ and $E = L \otimes_K K_\infty$, and equip $\mathrm{GL}_2(E)$ with its Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57). Fix a Haar measure $\nu_A$ on $K_\infty^\times$, a measure $\nu$ on $\mathrm{GL}_2(E)$, an additive Haar measure $\lambda$ on $E$, a Haar measure $\rho$ on $E^\times$, a Haar measure $\kappa$ on the subgroup $\mathbf{K}$ of $\mathrm{GL}_2(E)$ consisting of those $g$ whose image under [`AutomorphicForm.archIdentGL`](def/AutomorphicForm_TwistedOrbital.html#L424) lies, at every infinite place $w$ of $L$, in the group of $k \in \mathrm{GL}_2(L_w)$ with $\|\det k\| = 1$ for which $(x,y) \mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserves $\|x\|^2+\|y\|^2$, and a constant $c \in [0,\infty]$. Assume the Iwasawa formula $\int_{\mathrm{GL}_2(E)} \varphi \, d\nu = c \int_{(E^\times)^2} \int_E \int_{\mathbf{K}} \varphi(\mathrm{diag}(a_1,a_2)\, n(x)\, k)\, d\kappa\, d\lambda\, d(\rho \times \rho)$ for all Borel $\varphi : \mathrm{GL}_2(E) \to [0,\infty]$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\mathrm{diag}$ is `diagUnits2`. Write $\iota(p) = \mathrm{diag}(1 \otimes p_1, 1 \otimes p_2)$ for $p \in (K_\infty^\times)^2$, the image of $\mathrm{diag}(p_1,p_2)$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71). Let $F : \mathrm{GL}_2(E) \to [0,\infty]$ be Borel with $F(\iota(p)x) = F(x)$ for all $p, x$; let $\beta, w : \mathrm{GL}_2(E) \to \mathbb{R}$ be Borel and non-negative with $\int_{(K_\infty^\times)^2} \beta(\iota(p)\,\mathrm{diag}(a_1,a_2))\, d(\nu_A \times \nu_A) = 1$ for every $a \in (E^\times)^2$, and $\int_{(K_\infty^\times)^2} w(\iota(p)x)\, d(\nu_A \times \nu_A) = 1$ for every $x$ with $F(x) \neq 0$. Then $\int F \cdot w \, d\nu$ equals $c \int_{(E^\times)^2} \beta(\mathrm{diag}(a_1,a_2)) \int_E \int_{\mathbf{K}} F(\mathrm{diag}(a_1,a_2)\, n(x)\, k)\, d\kappa\, d\lambda\, d(\rho \times \rho)$, all integrals being $[0,\infty]$-valued apart from those of the real functions $\beta$ and $w$.
--
--   This is the archimedean step allowing a cut-off weight $w$ along the $(K_\infty^\times)^2$-orbits to be traded, inside the Iwasawa coordinates $\mathrm{diag}(a)n(x)k$ on $\mathrm{GL}_2(L \otimes_K K_\infty)$, for an arbitrary section weight $\beta$ on the torus, at the cost of inserting $\beta(\mathrm{diag}(a))$ in the $a$-integral. It is used in the estimate for twisted orbital integrals of conjugation-twisted automorphic forms at the infinite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (c : ℝ≥0∞)
    (hIw : ∀ φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] φ →
        @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν φ =
          c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
                φ (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x *
                  (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂lam ∂(ρ.prod ρ))
    (F : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hFm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] F)
    (hF : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        F (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) = F x)
    (β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1)
    (w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), F x ≠ 0 →
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            w (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) ∂(νA.prod νA) = 1) :
    @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν (fun x => F x * ENNReal.ofReal (w x)) =
      c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
                F (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂lam
          ∂(ρ.prod ρ) := by sorry
