-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/17f89d0a-fdae-545f-88ab-10980d43a0d3
-- title:
--   Casimir trichotomy at a real place for cuspidal constituents
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T}(\cdot\,x)\,[\,\Sigma\,]$ of right translates of the centre-cut Siegel set $\Sigma=$ `centreCutSiegelSet K c u d₁ d₂` (those $g$ whose finite part lies in the integral subgroup, with $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` in $[d_1,d_2]$ at every infinite place) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, in the sense that each $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,z\in D$. Let `pins` be the production carrier data on $D$ with Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, full central group, level groups `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen`, and additive Haar conditioned on `adelicBox K`; let $\xi$ be a character of its central group (the whole idele unit group) with $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{w_0}$ for a real $w_0$. Let $V$ be a complex subspace of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ lies in the $K$-finite cusp space of central character $\xi$, is stable under right translation by the finite adelic subgroup and by the rotation subgroups at the infinite places and under right convolution by factorisable archimedean-bi-finite test functions, is non-zero, and contains no proper non-zero such subspace. Assume for some non-zero ideal $N$ and some archimedean type family `tys` that $V$ intersected with the $U(N)$-invariants and with the type-cut submodule for `tys` is non-zero, that every infinite place of $K$ is real, and fix a real place $w$. Let $\lambda\in\mathbb{C}$ be such that every $x\in V$ is archimedean-smooth at $w$ and satisfies `archCasimirAt` $x=\lambda\,x$, the Casimir being $-\bigl(\tfrac14 H^2-\tfrac12 H+EF^-\bigr)$ in the derivation normalisation at $w$. Then $\lambda$ is real, and one of the following holds: its real part is positive; or there is an integer $k_0\ge 2$ with $\lambda=\tfrac{k_0}{2}\bigl(1-\tfrac{k_0}{2}\bigr)$ such that for every integer $n$, every non-zero ideal $N'$, every type family `tys'` and every non-zero $x$ in $V$ intersected with the $U(N')$-invariants and the `tys'` type cut which carries some integral weight character `archWeightCharAt` at each real place and the weight character of index $n$ at $w$ (in the sense of `HasArchCharacterAt₀`), one has $k_0\le|n|$ and $n\equiv k_0 \bmod 2$; or $\lambda=0$ and every $x\in V$ satisfies $x(g\cdot\mathrm{archRealGLAt}(h))=x(g)$ for all $g$ and all $h\in\mathrm{GL}_2(\mathbb{R})$ of determinant $1$.
--
--   This is the package of constraints that unitarity imposes on the archimedean component of a cuspidal constituent at a real place, in Bargmann's classification of the irreducible unitary representations of $\mathrm{SL}_2(\mathbb{R})$: positive Casimir (principal, complementary and limit-of-discrete series), discrete series of lowest weight $k_0\ge2$ with the corresponding weight gap and parity, or trivial archimedean action. It feeds the packaging of the core archimedean hypotheses used downstream in the analysis of automorphic forms on $\mathrm{GL}_2$ over a totally real field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
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
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x) :
    lam.im = 0 ∧
      (0 < lam.re ∨
        (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) ∧
          ∀ (n : ℤ) (N' : Ideal (𝓞 K)) (tys' : AutomorphicForm.ArchTypeFamily K) (x : AdelicGL2 (𝓞 K) K → ℂ),
            N' ≠ ⊥ → x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) N' ⊓ archCutSubmodule K tys' →
            (∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) x) →
            HasArchCharacterAt₀ K w (archWeightCharAt hw n) x → x ≠ 0 → (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
        (lam = 0 ∧ ∀ x ∈ V, ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g)) := by sorry
