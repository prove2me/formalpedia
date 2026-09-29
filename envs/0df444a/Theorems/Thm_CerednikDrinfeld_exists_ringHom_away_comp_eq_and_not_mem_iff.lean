-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff
-- name    : CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/985889ef-4871-5aa6-8db9-bf309069bedc
-- title:
--   Localisation away from an element is functorial; basic opens pull back
-- statement:
--   Let $B$ and $B'$ be commutative rings, $f\colon B\to B'$ a ring homomorphism and $g\in B$. The assertion is a conjunction of two statements. First, there exists a ring homomorphism $f_g\colon B_g\to B'_{f(g)}$ between the localisations away from $g$ and away from $f(g)$ (that is, `Localization.Away g` and `Localization.Away (f g)`) such that the composite of the structure map $B\to B_g$ followed by $f_g$ equals the composite of $f$ followed by the structure map $B'\to B'_{f(g)}$; in other words $f_g$ is compatible with $f$ over the two canonical algebra maps. Secondly, for every prime $x'$ of $B'$, regarded as a point of `PrimeSpectrum B'` with underlying prime ideal $x'$, one has $f(g)\notin x'$ if and only if $g$ is not in the prime ideal underlying `PrimeSpectrum.comap f x'`, i.e. not in $f^{-1}(x')$. Thus the basic open locus $D(f(g))$ of $\operatorname{Spec} B'$ is exactly the preimage under $\operatorname{Spec}(f)$ of the basic open locus $D(g)$ of $\operatorname{Spec} B$. No hypotheses beyond the commutative ring structures are imposed.
--
--   This is the elementary functoriality of localisation at the powers of an element, together with the compatibility of basic opens with the induced map of prime spectra. It is used in the Čerednik–Drinfeld part of the development, in the treatment of Cartier quadruples and their behaviour under base change and under maps of rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff
    {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) = (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by sorry
