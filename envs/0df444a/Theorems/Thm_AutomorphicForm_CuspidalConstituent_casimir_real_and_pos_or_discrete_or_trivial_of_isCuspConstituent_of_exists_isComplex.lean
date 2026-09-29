-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex
-- name    : AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c917b693-579b-5f44-aa26-e11503472525
-- title:
--   Casimir trichotomy at a real place for cuspidal constituents
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the set $D=\bigcup_{x\in T}(\cdot\, x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\,]$ covers modulo the centre, i.e. every $g$ can be written so that $\gamma g z \in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (pushed to the adeles) and some $z\in\mathbb{A}_K^\times$ (acting as a central scalar). Work with the carrier data `productionPinsOf` attached to $D$, to the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap \mathrm{finiteAdelicGL2Subgroup}$, to the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and to the box `adelicBox K`; its central subgroup is all of $\mathbb{A}_K^\times$, so $\xi$ is a homomorphism $\mathbb{A}_K^\times\to\mathbb{C}^\times$. Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$: $V$ lies in the $K$-finite cuspidal submodule, is stable under right translation by the finite adelic subgroup, by the rotation subgroups `rowIsometrySubgroup₀` at the infinite places and under right convolution by factorizable archimedean-bi-finite test functions, is non-zero, and has no proper non-zero submodule with these stability properties. Assume $\|\xi(z)\| = \mathrm{ideleNorm}(z)^{w_0}$ for all $z$, for some real $w_0$; assume that for some non-zero ideal $N$ and some archimedean type family $\mathrm{tys}$ the intersection of $V$ with the $N$-level invariants (functions right invariant under $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$) and with the type cut `archCutSubmodule K tys` is non-zero; assume $K$ has at least one complex place. Let $w$ be a real place and $\lambda\in\mathbb{C}$ such that every $x\in V$ is smooth at $w$ in the sense of `IsArchSmoothAt` and satisfies $\mathrm{archCasimirAt}\,x=\lambda x$, the Casimir being $-\bigl(\tfrac14 H^2-\tfrac12 H+EF\bigr)$ in the one-parameter derivations at $w$. Then $\lambda$ is real, and either $\operatorname{Re}\lambda>0$; or there is a natural number $k_0\ge 2$ with $\lambda=\tfrac{k_0}{2}\bigl(1-\tfrac{k_0}{2}\bigr)$ such that for every $n\in\mathbb{Z}$, every non-zero ideal $N'$, every type family $\mathrm{tys}'$ and every non-zero $x$ in the intersection of $V$ with the $N'$-level invariants and the cut for $\mathrm{tys}'$ which carries some integral weight character at each real place and carries the weight-$n$ character `archWeightCharAt hw n` at $w$ (in the sense of `HasArchCharacterAt₀`, the character being the $n$-th power of the basic weight-one character of the rotation subgroup at $w$), one has $k_0\le|n|$ and $n\equiv k_0 \pmod 2$; or $\lambda=0$ and every $x\in V$ satisfies $x(g\cdot \mathrm{archRealGLAt}\,h)=x(g)$ for all $g$ and all $h\in\mathrm{GL}_2(\mathbb{R})$ of determinant $1$.
--
--   This is the list of constraints that unitarity imposes on the archimedean component of a cuspidal constituent at a real place, in the shape of Bargmann's classification of the irreducible unitary representations of $\mathrm{SL}_2(\mathbb{R})$: positive Casimir eigenvalue (principal, complementary and limit-of-discrete cases), discrete series of lowest weight $k_0\ge2$ with the weight gap and parity condition, or the locally trivial case. It is the complex-place version of the trichotomy and feeds the weight-$k_0$ extraction used in the archimedean analysis of cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex.lean

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

theorem AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex
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
    (hcx : ∃ v : InfinitePlace K, v.IsComplex)
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
