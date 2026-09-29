-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
-- name    : AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4a6182ab-b6e4-59bd-8cdd-222f0f0636ab
-- title:
--   Central character determined by Hecke eigenvalues away from a finite set
-- statement:
--   Let $K$ be a number field and let $D$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Let $\Theta,\Theta'$ be Hecke eigensystems over $K$ with complex coefficients, i.e. data consisting of a nonzero level ideal of $\mathcal{O}_K$ together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places, and assume $\Theta$ and $\Theta'$ agree away from a finite set: there is a finite set $S$ of primes with $a_v(\Theta)=a_v(\Theta')$ and $b_v(\Theta)=b_v(\Theta')$ for all $v\notin S$. Fix the carrier data `productionPinsOf` attached to $D$: the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the window $D$, the central subgroup $Z=\mathbb{A}_K^{\times}$ (the top subgroup), the level groups $N\mapsto \mathrm{levelOne}(N)\cap \ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$, and the additive adelic Haar measure conditioned on `adelicBox`. For an eigensystem $\Phi$, a `SmoothCuspRealizationAt` consists of a function $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is somewhere nonzero, a central character $\omega:Z\to\mathbb{C}^{\times}$, the hypothesis that $\varphi$ is a cuspidal automorphic function with central character $\omega$ and is $K_f$-smooth, right invariance of $\varphi$ under the level group at $\Phi$'s level, and a finite exceptional set outside which $\varphi$ is a Hecke coset eigenfunction with eigenvalue $a_v(\Phi)$ at $\mathrm{heckeGen}(v)$ and satisfies $\varphi(\mathrm{centralScalar}(\det \mathrm{heckeGen}(v))\,g)=b_v(\Phi)\varphi(g)$ for all $g$. Let $R$ be such a realization for the raw-central rescaling of $\Theta$ (same level and same $a_v$, with $b_v$ replaced by $(\mathrm{N}v)^{-1}b_v$) and $R'$ one for the raw-central rescaling of $\Theta'$, and assume both are genuine, that is, $R$'s and $R'$'s underlying functions are continuous. Then the two central characters coincide: $R.\mathrm{centralChar}=R'.\mathrm{centralChar}$ as homomorphisms $\mathbb{A}_K^{\times}\to\mathbb{C}^{\times}$.
--
--   This is the uniqueness statement saying that the central character of an adelic cuspidal realization is pinned down by the Hecke data at almost all primes, so that eigensystems agreeing outside a finite set of places cannot be realized with different central characters. It feeds the comparison results on archimedean weights and coverage modulo the centre that are used when matching realizations attached to related eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite
    (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    R.centralChar = R'.centralChar := by sorry
