-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
-- name    : AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/459fbb26-f732-5539-a16b-b669063a94c9
-- title:
--   Local Sobolev bound on adelic GL₂ via archimedean derivative words
-- statement:
--   Let $K$ be a number field, $N\neq 0$ an ideal of $\mathcal O_K$, and let $\mathrm{GL}_2(\mathbb A_K)$ denote `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring, carried with its Borel $\sigma$-algebra and Haar measure `adelicGLHaar`. Fix, for each real place $w$, a group homomorphism $\omega_{w}:\mathbb R^\times\to\mathbb C^\times$ with $t\mapsto\omega_w(t)$ continuous as a map to $\mathbb C$, and for each complex place $w$ a homomorphism $\omega_w:\mathbb C^\times\to\mathbb C^\times$, likewise continuous; let $C\subseteq \mathrm{GL}_2(\mathbb A_K)$ be compact. For a list $l$ of direction labels — each label being either a real place $w$ together with a witness of its reality and an element of $\{H,E,F\}$, or a complex place with a witness and one of the six directions `ArchDirComplex` — write $W_l b$ for the result of applying the corresponding one-parameter derivations, in right-to-left order, to $b$, where the real-place derivation sends $\varphi$ to $g\mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,d\,t)|_{t=0}$ and the complex-place one is the analogous `archDerivAtComplex`. Then there exist a compact set $C'\supseteq C$ and a constant $c\ge 0$ such that the following holds for every $b:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$: if $b(gu)=b(g)$ for all $g$ and all $u$ in the intersection of `principalLevel (𝓞 K) K N` (the level-$N$ group intersected with its conjugate by the Weyl element) with the kernel `finiteAdelicGL2Subgroup K` of the archimedean projection; if $b(g\cdot\iota_w(\mathrm{scalar}\,t))=\omega_w(t)\,b(g)$ at every real place for all $t\in\mathbb R^\times$ and correspondingly at every complex place for all $z\in\mathbb C^\times$, where $\iota_w$ denotes the embedding of $\mathrm{GL}_2$ of the completion at $w$; and if for every word $l$ of length at most $4\,r_1(K)+8\,r_2(K)$ the function $W_l b$ is continuous and satisfies `IsArchSmoothAt` at every real place and `IsArchSmoothAtComplex` at every complex place (i.e. is $C^\infty$ on the invertible locus in matrix-entry charts at that place); then for every $M\ge 0$ with $\|W_l b\|_{L^2(C',\,\mathrm{adelicGLHaar})}\le M$ for all such $l$, one has $\lVert b(x)\rVert\le c\,M$ for every $x\in C$. The constant $c$ and the set $C'$ depend on $K$, $N$, $C$ and the characters $\omega_w$ only, not on $b$ or $M$.
--
--   This is the local Sobolev (elliptic) estimate on the adelic group: the supremum over a compact set of a function invariant under a principal congruence subgroup and transforming by fixed characters of the archimedean centres is controlled by the $L^2$ norms, over a slightly larger compact set, of its words of bounded length in the invariant archimedean derivations. It is used in the bound for elements of the isotypic cusp space with prescribed Casimir eigenvalue, where it converts an $L^2$ bound into a pointwise one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal), Continuous fun t : ℝˣ => ((ωR w hw t : ℂˣ) : ℂ))
    (ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), Continuous fun z : ℂˣ => ((ωC w hw z : ℂˣ) : ℂ))
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧ C ⊆ C' ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
              ((ωR w hw t : ℂˣ) : ℂ) * b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
              ((ωC w hw z : ℂˣ) : ℂ) * b g) →
        (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
            eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C') ≤ ENNReal.ofReal M) →
          ∀ x ∈ C, ‖b x‖ ≤ c * M := by sorry
