-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
-- name    : AutomorphicForm.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/99a84f74-595e-58c7-97a2-b713718877f1
-- title:
--   Smoothing isotypic cusp forms into a Siegel-window isotypic space
-- statement:
--   Let $K$ be a number field, and let $\alpha<\beta$ be real numbers with $\beta>0$. Let $\Phi\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to the slab $\{g:\lVert\det g\rVert\in[\alpha,\beta]\}$, the norm being the idele norm given by the modulus of the translation action on $\mathbb{A}_K$. Fix a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_K)$ indexed by ideals of $\mathcal{O}_K$, a character $\xi$ of the full idele unit group, an ideal $N$ with $U(N)$ contained in the kernel of the archimedean projection `glArch`, a finite set $S$ of finite places, an archimedean type family `tys` (for each infinite place $w$, finitely many representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$), a Hecke eigensystem $\pi$ with complex eigenvalues, reals $c,u,d_1,d_2$ with $c>0$ and $d_1>0$, and a finite set $T\subseteq\mathrm{GL}_2(\mathbb{A}_K)$. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth in the matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported, such that every $x$ with $f(x)\neq0$ factors as $x=ak$ with $a$ of trivial finite part and $k\in U(N)$, and such that $f$ is invariant under conjugation by `rowIsometryInclAt₀ K w k` for every infinite place $w$ and every $k$ in the row-isometry subgroup of $\mathrm{GL}_2(K_w)$. Then for every $\varphi$ lying in the intersection of `archCutSubmodule K tys` (the infimum over infinite places $w$ of the supremum of the type submodules of the representations `tys.rep w i`) with the isotypic cusp submodule — the $\mathbb{C}$-span of the continuous, right $U(N)$-invariant functions satisfying `IsSmoothCuspAutomorphicFnAt` for the carrier data `productionPinsOf K Φ U (heckeGen) (adelicBox K)` and $\xi$, which are Hecke coset eigenfunctions with eigenvalue $\pi.a(v)$ for the generator `heckeGen` at each $v\notin S$ and satisfy $\varphi(z(\det(\mathrm{heckeGen}\,v))g)=\pi.b(v)\varphi(g)$ there — the right convolution $g\mapsto\int\varphi(gx)f(x)\,dx$ against the adelic Haar measure again lies in the intersection with `archCutSubmodule K tys` of the isotypic cusp submodule for the same $\xi,N,S,\pi$ but with the domain $\Phi$ replaced by the union over $x\in T$ of the right translates by $x$ of the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (elements with integral finite part whose archimedean component at every infinite place has local height at least $c$, window quantity `xWindowSq` at most $u^2$, and determinant norm in $[d_1,d_2]$). The parameters $u$, $d_2$ and the finite set $T$ are otherwise unconstrained.
--
--   This is the Godement-style smoothing step: convolution on the right by a test function supported over the level group and invariant under conjugation by the archimedean row-isometry subgroups preserves the cuspidal, Hecke-isotypic and archimedean-type conditions while replacing the fundamental-domain carrier by a centre-cut Siegel window. It is used in the proof that the isotypic cuspidal space at principal level, cut by archimedean types, is finite-dimensional, and in the comparison of such spaces across carriers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain_of_pos
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hU : U N ≤ finiteAdelicGL2Subgroup K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hfs : ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U N ∧ x = a * k)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) :
    ∀ φ ∈ isotypicCuspSubmodule K (productionPinsOf K Φ U (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          ξ N S π ⊓ archCutSubmodule K tys,
      rightConv K φ f ∈ isotypicCuspSubmodule K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π
        ⊓ archCutSubmodule K tys := by sorry
