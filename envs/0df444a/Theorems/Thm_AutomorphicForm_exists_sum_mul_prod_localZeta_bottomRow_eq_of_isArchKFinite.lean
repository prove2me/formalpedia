-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
-- name    : AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a925e829-b289-583a-8d54-f8548008732f
-- title:
--   Archimedean Godement sections realise K_∞-finite functions on GL₂
-- statement:
--   Let $F$ be a number field, equip each completion $F_w$ at an infinite place $w$ with a Borel measurable structure and an additive Haar measure $\mu_{a,w}$, and let $\mu,\nu:\mathbb A_F^\times\to\mathbb C^\times$ be homomorphisms all of whose values have modulus $1$ and which are continuous as $\mathbb C$-valued functions. Let $U:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be continuous and satisfy `IsArchKFinite`, i.e. for every infinite place $w$ the right translates of $U$ by `archRowIsometrySubgroup F w` span a finite-dimensional space, and assume $U(bg)=\mu(b_{00})\,\nu(b_{11})\,U(g)$ for all $g$ and all $b$ with $b_{10}=0$, trivial finite part $\mathrm{glFin}\,b=1$, and all archimedean components row isometries (determinant of norm $1$, and $(x,y)\mapsto(xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserving $\|x\|^2+\|y\|^2$). Then there exist $m\in\mathbb N$, Schwartz functions $g_j$ on $(F\otimes\mathbb R)^2$ in the mixed-space model, families $\Phi_{j,w}:F_w^2\to\mathbb C$, and entire functions $E_j:\mathbb C\to\mathbb C$, such that each $g_j$ factorises as $g_j(y)=\prod_w\Phi_{j,w}(y_w)$ under the identification of $(\mathbb A_{F,\infty})^2$ with the mixed space, and such that for every $z$ with $\operatorname{Re}z>0$ and every $k$ in `adelicMaximalCompact F` with $\mathrm{glFin}\,k=1$, $$\sum_j E_j(z)\,\mu(\det k)\prod_w Z_{F_w}\!\big(t\mapsto\Phi_{j,w}(t\cdot(k_w)_{1\bullet}),\,(\mu\nu^{-1})_w,\,z\big)=U(k),$$ where $Z_{F_w}$ is Tate's local zeta integral [`LanglandsTunnell.TateLocal.localZeta`](def/LanglandsTunnell_TateLocalZeta.html#L125) for $\mu_{a,w}$, $(k_w)_{1\bullet}$ is the second row of the component of $k$ at $w$, and $(\mu\nu^{-1})_w$ is $\mu\nu^{-1}$ composed with `archUnitHom w`.
--
--   This is the archimedean half of the assertion that Godement sections attached to factorisable Schwartz functions exhaust the $K$-finite vectors of the induced representation: every continuous, $K_\infty$-finite function on $\mathrm{GL}_2(\mathbb A_F)$ transforming under the upper-triangular elements of $K_\infty$ by $(\mu,\nu)$ is recovered on $K_\infty$ as a finite combination, with entire coefficients, of products of local zeta integrals along bottom rows. It feeds the construction of flat families of Godement sections and the comparison of their global zeta integrals with partial Euler products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal SchwartzMap

open scoped Classical in

theorem AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
    (F : Type) [Field F] [NumberField F]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (g : Fin m → 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
      (Φa : Fin m → (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
      (E : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (E j)) ∧
      (∀ j (y : Fin 2 → InfiniteAdeleRing F),
        g j (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φa j w (fun i => y i w)) ∧
      ∀ (z : ℂ), 0 < z.re →
        ∀ (k : AdelicGL2 (𝓞 F) F), k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
          (∑ j, E j z * (((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                  (fun t => Φa j w (fun i => t
                    * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (archLocalChar (μ * ν⁻¹) w) z))
            = U k := by sorry
