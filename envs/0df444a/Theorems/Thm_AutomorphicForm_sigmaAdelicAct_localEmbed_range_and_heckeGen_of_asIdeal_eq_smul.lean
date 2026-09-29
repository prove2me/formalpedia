-- Prove2me | Theorems.Thm_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
-- name    : AutomorphicForm.sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/dafff97c-f1e6-5e6b-9368-86979069b574
-- title:
--   Galois action permutes local factors and Hecke generators
-- statement:
--   Let $K$ be a field and $L$ a number field with a $K$-algebra structure, let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) datum for $\mathcal{O}_L$ over $K$ and $L$ — that is, a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, compatible with the Galois action on principal adeles and continuous in each $\sigma$ — and let $\sigma : L \simeq_{\mathrm{alg}[K]} L$. Let $w, w'$ be height-one primes of $\mathcal{O}_L$ with $w'.\mathrm{asIdeal} = \sigma \bullet w.\mathrm{asIdeal}$ (pointwise translate). Write $\sigma_D$ for `sigmaAdelicAct K L D σ`, the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma$ entrywise, $\iota_w$ for [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), which sends $g \in \mathrm{GL}_2(L_w)$ to the finite-adelic matrix whose entries agree with $g$ at $w$ and with those of the identity matrix elsewhere, and $j$ for [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145), which pairs a finite-adelic matrix with the identity matrix over the infinite adeles. Three assertions are made. First, $\sigma_D$ carries the subgroup $j(\iota_w(\mathrm{GL}_2(L_w)))$ onto $j(\iota_{w'}(\mathrm{GL}_2(L_{w'})))$. Second, there is $u$ in [`AdelicDock.localLevelOne (𝓞 L) L w' ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the group of $g \in \mathrm{GL}_2(L_{w'})$ for which $\iota_{w'}(g)$ and its inverse satisfy the predicate `IsLevelOneMatrix` for the level ideal $\top$, with $\sigma_D(\mathrm{heckeGen}_w) = \mathrm{heckeGen}_{w'} \cdot j(\iota_{w'}(u))$, where $\mathrm{heckeGen}_w$ is the image under `heckeGenAt` of the uniformiser unit at $w$. Third, $\sigma_D$ carries $j(\iota_w(\mathrm{localLevelOne}\ w\ \top))$ onto $j(\iota_{w'}(\mathrm{localLevelOne}\ w'\ \top))$.
--
--   This is the equivariance of the adelic Galois action with respect to the local factors at finite places: $\sigma$ transports the place $w$ to the place $w'$ determined by $\sigma \bullet w.\mathrm{asIdeal}$, matching local subgroups with local subgroups, integral level-one subgroups with integral level-one subgroups, and the Hecke generator at $w$ with that at $w'$ up to a right factor from the integral subgroup at $w'$. It is used in the proof of [`AutomorphicForm.exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul`](thm.html#AutomorphicForm.exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul), where Hecke words at a place are moved by a Galois twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw' : w'.asIdeal = σ • w.asIdeal) :
    ((AdelicDock.localEmbed (𝓞 L) L w).range.map (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = (AdelicDock.localEmbed (𝓞 L) L w').range.map (AdelicDock.finEmbed (𝓞 L) L) ∧
      (∃ u ∈ AdelicDock.localLevelOne (𝓞 L) L w' ⊤,
        sigmaAdelicAct K L D σ (heckeGen (𝓞 L) L w)
          = heckeGen (𝓞 L) L w' * AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w' u)) ∧
      (((AdelicDock.localLevelOne (𝓞 L) L w ⊤).map (AdelicDock.localEmbed (𝓞 L) L w)).map
            (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = ((AdelicDock.localLevelOne (𝓞 L) L w' ⊤).map (AdelicDock.localEmbed (𝓞 L) L w')).map
            (AdelicDock.finEmbed (𝓞 L) L) := by sorry
