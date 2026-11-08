-- Prove2me | Theorems.Thm_FairFacilityLoc_lemma_3_2
-- name    : FairFacilityLoc.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:36.633138+00:00
-- url     : https://prove2.me/theorems/06b440cd-557f-456c-9ca0-c7a42fa0cf7e
-- title:
--   Lemma 3.2 — the cut rule is well defined, strategyproof and coordinate-independent
-- statement:
--   For each coordinate $r$, fix winning sets of agents that do not depend on the reports, and assume that every set containing a winning set is winning, that $N$ is winning and that $\emptyset$ is not winning. The mechanism that returns, in each coordinate $r$, the smallest report $t\in\{x_{1r},\dots,x_{nr}\}$ whose left set $L_r(t;x)$ is winning is well defined, strategyproof and coordinate-independent.
--
--   This is the general source of strategyproofness in the mission: it applies to $M_d$ in every dimension.
--
--   Differences from the source:
--   - encoding: well defined → the IsLeast clause for the candidate set; reason: the output is written with sInf, and IsLeast says the printed minimum exists and is the output
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_FairFacilityLoc_cutOutput

namespace FairFacilityLoc

/-- **Lemma 3.2** (Yan, Zhou, manuscript, sha256 642a1268…, p.17, PDF p.19). For winning sets fixed per coordinate,
upward closed, with `N` winning and `∅` not winning, the mechanism returning in each coordinate the smallest report
with a winning left set is well defined, strategyproof and coordinate-independent.

**Formalization Note.** "Well defined" is the `IsLeast` clause. `Win` has no profile argument, and a group structure
enters only through the choice of `Win`. -/
theorem lemma_3_2 {n d : ℕ} (Win : Fin d → Finset (Fin n) → Prop)
    (h_mono : ∀ r S S', S ⊆ S' → Win r S → Win r S')
    (h_univ : ∀ r, Win r Finset.univ) (h_empty : ∀ r, ¬ Win r ∅) :
    (∀ (x : Fin n → GeoSemialgCSP.E d) (r : Fin d), IsLeast (cutCandidates Win x r) (cutOutput Win x r)) ∧
      (∀ (x : Fin n → GeoSemialgCSP.E d) (i : Fin n) (x' : GeoSemialgCSP.E d),
        ‖x i - cutOutput Win x‖ ≤ ‖x i - cutOutput Win (Function.update x i x')‖) ∧
      (∀ (r : Fin d) (x x' : Fin n → GeoSemialgCSP.E d),
        (∀ i, x i r = x' i r) → cutOutput Win x r = cutOutput Win x' r) := by sorry

end FairFacilityLoc
