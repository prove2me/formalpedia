-- Prove2me | Theorems.Thm_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
-- name    : AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/822d558d-46ab-5147-afa8-b7ccec5722af
-- title:
--   Smoothness and sphericity outside S give right K^S-invariance
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of nonzero prime ideals of $\mathcal O_K$, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $K$ (the group `AdelicGL2 (𝓞 K) K`). Assume first that $\varphi$ is $K_f$-smooth, i.e. that inside the subgroup of $\mathrm{GL}_2(\mathbb A_K)$ consisting of the elements with trivial archimedean part (the kernel of `glArch`), the stabiliser of $\varphi$ for the right-translation action is an open subset. Assume second that $\varphi$ is spherical outside $S$: for every prime $v \notin S$, every $k_v \in \mathrm{GL}_2(\mathcal O_{K_v})$ and every $g \in \mathrm{GL}_2(\mathbb A_K)$, one has $\varphi(g\cdot \iota_v(k_v)) = \varphi(g)$, where $\iota_v$ is the embedding [`UnramifiedWhittaker.placeEmbed`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) sending a matrix in $\mathrm{GL}_2(K_v)$ to the adelic matrix with that entry at $v$ and $1$ elsewhere, and $k_v$ is viewed in $\mathrm{GL}_2(K_v)$ entrywise. The conclusion is that $\varphi(g k) = \varphi(g)$ for every $g \in \mathrm{GL}_2(\mathbb A_K)$ and every $k$ in `maximalCompactAway K S`, the subgroup of elements $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K`, whose archimedean component at each infinite place of $K$ satisfies `IsRowIsometry`, whose archimedean part is trivial, and whose component at each $v \in S$ is trivial.
--
--   This is the standard passage from one-place-at-a-time sphericity to invariance under the full compact group $\mathbf{K}^S = \prod_{v \notin S} \mathrm{GL}_2(\mathcal O_v)$ away from $S$, the point being that smoothness supplies a finite set $S_0$ beyond which invariance is automatic. It is used to remove the compact variable from torus integrals of Whittaker functions and from Eisenstein sections unramified outside $S$, and is cited in the Rankin–Selberg integral constructions and in the cuspidal realisation results of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (_hφ : IsKfSmooth K φ)
    (_hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) :
    ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g := by sorry
