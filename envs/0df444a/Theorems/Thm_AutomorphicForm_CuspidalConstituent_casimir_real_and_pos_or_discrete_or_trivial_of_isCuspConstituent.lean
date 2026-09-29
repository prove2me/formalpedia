-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7948fd6e-567d-5603-bcdc-05127dc3870a
-- title:
--   Unitarity constraints on the Casimir eigenvalue at a real place
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the finite union $D=\bigcup_{x\in T} (\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\ K\ c\ u\ d_1\ d_2\,]$ of right translates of the centre-cut Siegel set (finite part in the integral subgroup, local height $\ge c$ at every infinite place, window $\mathrm{xWindowSq}\le u^2$, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place) satisfies `CoversModCentre`: every $g$ can be moved into $D$ by a global point on the left and a central idele on the right. Fix the carrier data `productionPinsOf` attached to $D$, with level subgroups $U(N)=\mathrm{levelOne}(N)\cap\mathrm{GL}_2(\mathbb{A}_{K,f})$, Hecke generators $\mathrm{heckeGen}$ and box $\mathrm{adelicBox}$; its central subgroup is all of $\mathbb{A}_K^\times$, so $\xi$ is a character of the full idele unit group, assumed to satisfy $\lVert\xi(z)\rVert=\lVert z\rVert^{w_0}$ for a real $w_0$, the norm being the module of the Haar character. Let $V$ be a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a cuspidal constituent for these data and $\xi$: $V$ lies in the $K_\infty^1$-finite cuspidal submodule, is stable under right translation by the finite adelic subgroup and by the subgroups $\mathrm{rowIsometrySubgroup}_0$ at all infinite places and under right convolution by factorizable archimedean-bi-finite test functions, is non-zero, and is minimal with these properties. Assume moreover that for some non-zero ideal $N$ and some finite family $\mathrm{tys}$ of archimedean types the intersection of $V$ with the $U(N)$-invariants and with the type-cut submodule $\mathrm{archCutSubmodule}\ K\ \mathrm{tys}$ is non-zero. Let $w$ be a real place and $\lambda\in\mathbb{C}$ such that every $x\in V$ is smooth in the real matrix coordinates at $w$ (`IsArchSmoothAt`) and satisfies $\mathrm{archCasimirAt}\ x=\lambda x$. Then $\lambda$ is real, and one of three alternatives holds: either $\operatorname{Re}\lambda>0$; or there is a natural number $k_0\ge 2$ with $\lambda=\frac{k_0}{2}\bigl(1-\frac{k_0}{2}\bigr)$ such that for every integer $n$, every non-zero ideal $N'$, every type family $\mathrm{tys}'$ and every non-zero $x$ in the intersection of $V$ with the $U(N')$-invariants and $\mathrm{archCutSubmodule}\ K\ \mathrm{tys}'$ which satisfies the weight condition `HasArchCharacterAt₀` for some integral weight character $\mathrm{archWeightCharAt}$ at every real place and for the weight $n$ at $w$, one has $k_0\le|n|$ and $n\equiv k_0 \pmod 2$; or $\lambda=0$ and every $x\in V$ satisfies $x(g\cdot \mathrm{archRealGLAt}\,h)=x(g)$ for all $g$ and all $h\in\mathrm{GL}_2(\mathbb{R})$ of determinant $1$.
--
--   This is Bargmann's classification of the irreducible unitary representations of $\mathrm{SL}_2(\mathbb{R})$, in the form of the constraints that unitarity of a cuspidal constituent imposes at a real place: positive Casimir eigenvalue (principal, complementary and limit-of-discrete series), discrete series of lowest weight $k_0\ge 2$ with the attendant weight gap and parity, or trivial action of the norm-one archimedean group. It feeds the assembly of the core hypotheses attached to vectors in the level-and-type cut, via [`AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt`](thm.html#AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent.lean

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

theorem AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent
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
