-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/cb4ee190-5e10-5ca9-bd58-4ed15a6e0c8c
-- title:
--   SU(2)-string decomposition of cut vectors at a complex place
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that $D=\bigcup_{x\in T}\{g x : g\in\mathfrak S\}$, where $\mathfrak S$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, local height $\ge c$, $x$-window $\le u^2$ and archimedean determinant norm in $[d_1,d_2]$ at each infinite place), covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left $\mathrm{GL}_2(K)$ and central idelic translation. Let `pins` be `productionPinsOf K D` with level groups $N\mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean projection, Hecke generators the local uniformizer matrices, and box `adelicBox K`; its group `pins.Z` is all of $\mathbb{A}_K^\times$. Let $\xi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a character with $|\xi(z)|=\|z\|^{w_0}$ for a real $w_0$, and let $V$ be a cuspidal constituent for $(\mathrm{pins},\xi)$: a nonzero submodule of the $K$-finite cusp submodule, stable under right translation by finite-adelic elements and by the archimedean row-isometry subgroups and under right convolution by factorizable archimedean-bi-finite test functions, and minimal among such submodules. Let $N\ne 0$ be an ideal, `tys` a family of archimedean types, and let $X=V\cap\{\varphi:\varphi(g u)=\varphi(g)\ \forall u\in \mathrm{pins}.U(N)\}\cap$ `archCutSubmodule K tys` be nonzero. Let $w$ be a complex place, $y\in X$, and assume every element of $V$ is smooth at $w$, has continuous first and second flow derivatives in all six directions, and is an eigenvector of the two Casimir operators at $w$ with eigenvalues $\lambda,\lambda'$. Then there are $m\in\mathbb{N}$, lengths $n:\mathrm{Fin}\,m\to\mathbb{N}$, functions $x_{s,p}$ for $p\le n_s$, coefficients $c_{s,p}\in\mathbb{C}$ and matrix-valued maps $E_1,E_2:\mathrm{Fin}\,m\to\mathbb{R}\to M_{n_s+1}(\mathbb{C})$ with $y=\sum_s\sum_p c_{s,p}x_{s,p}$ and, for each $s$: all $x_{s,p}\in X$; $x_{s,0}\ne 0$; if $n_s=0$ then `HasArchCharacterAt₀ K w 1` holds for $x_{s,0}$ (the trivial archimedean condition at $w$); $D_{iH}x_{s,0}=i n_s\,x_{s,0}$ and $(D_{Fm}-D_E+i(D_{iE}+D_{iFm}))x_{s,0}=0$; each $x_{s,p}$ is continuous, invariant under left translation by $\mathrm{GL}_2(K)$ and satisfies $x_{s,p}(zg)=\xi(z)x_{s,p}(g)$ for central idelic $z$; every word of flow derivatives applied to $x_{s,p}$ is smooth at $w$ and continuous; $x_{s,p}$ has circle weight $n_s-2p$ at $w$; $E_1(s,0)=E_2(s,0)=1$, the entries of $E_1(s,\cdot)$ and $E_2(s,\cdot)$ are differentiable at $0$ with derivative matrices the ladder matrices having entries $1$ resp.\ $-j(n_s+1-j)$, and $i$ resp.\ $i\,j(n_s+1-j)$, on the two off-diagonals; the right translates of $x_{s,p}$ by the lifts to $w$ of $\begin{pmatrix}\cos r&-\sin r\\ \sin r&\cos r\end{pmatrix}$ and $\begin{pmatrix}\cos r&i\sin r\\ i\sin r&\cos r\end{pmatrix}$ are the combinations $\sum_{p'}E_1(s,r)_{p'p}x_{s,p'}$, resp.\ with $E_2$; each $x_{s,p}$ is a $\lambda$- and $\lambda'$-eigenvector of the two Casimirs; and for each $p$ there is $C_0\in\mathbb{R}$ with $\|W(x_{s,p})(g)\|\le C_0\|\det g\|^{w_0/2}$ for all $g$, where $W$ is the Whittaker coefficient at $\alpha=1$ against the standard additive character of $K$.
--
--   This is the $\mathfrak{sl}_2$-string (lowering-ladder) decomposition of a level-and-type cut vector in a cuspidal constituent of $\mathrm{GL}_2$ over a number field at a complex place, packaged so that each string member again carries all the data — cut membership, left $\mathrm{GL}_2(K)$-invariance, central character, smoothness, circle weight, explicit $SU(2)$ coordinate matrices, Casimir eigenvalues and the Whittaker growth bound — needed downstream. It is used in the derivation of the Whittaker-coefficient identities and decay estimates at finite-adelic translates with trivial archimedean component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex

    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : (s : Fin m) → Fin (n s + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
      (coef : (s : Fin m) → Fin (n s + 1) → ℂ)
      (E₁ E₂ : (s : Fin m) → ℝ → Matrix (Fin (n s + 1)) (Fin (n s + 1)) ℂ),
      y = ∑ s : Fin m, ∑ p : Fin (n s + 1), coef s p • x s p ∧
      ∀ s : Fin m,
        (∀ p, x s p ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
        (x s 0 ≠ 0) ∧
        (n s = 0 → HasArchCharacterAt₀ K w 1 (x s 0)) ∧
        (archDerivAtComplex hw .iH (x s 0) = (Complex.I * (n s : ℂ)) • x s 0) ∧
        (archDerivAtComplex hw .Fm (x s 0) - archDerivAtComplex hw .E (x s 0)
          + Complex.I • (archDerivAtComplex hw .iE (x s 0) + archDerivAtComplex hw .iFm (x s 0)) = 0) ∧
        (∀ p, Continuous (x s p)) ∧
        (∀ p (γ : GL (Fin 2) K) (g' : AdelicGL2 (𝓞 K) K), x s p (globalPoints (𝓞 K) K γ * g') = x s p g') ∧
        (∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (centralScalar (𝓞 K) K z * g') = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x s p g') ∧
        (∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x s p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x s p))) ∧
        (∀ p : Fin (n s + 1), HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℕ)) (x s p)) ∧
        (E₁ s 0 = 1) ∧
        (E₂ s 0 = 1) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₁ s r i j)
          (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₂ s r i j)
          (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), -(Real.sin r : ℂ); (Real.sin r : ℂ), (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₁ s r p' p * x s p' g') ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), (Real.sin r : ℂ) * Complex.I; (Real.sin r : ℂ) * Complex.I, (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₂ s r p' p * x s p' g') ∧
        (∀ p, archCasimirAtComplex hw (x s p) = lam • x s p ∧ archCasimirBarAtComplex hw (x s p) = lam' • x s p) ∧
        (∀ p, ∃ C₀ : ℝ, ∀ g' : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 g'‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g') ^ (w₀ / 2)) := by sorry
