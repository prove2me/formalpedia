-- Prove2me | Theorems.Thm_FasterSFM_lemma_6
-- name    : FasterSFM.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:33.528281+00:00
-- url     : https://prove2.me/theorems/78f89d80-5725-4936-8658-d2647721d245
-- title:
--   Lemma 6 — a block containing the head of a new arc
-- statement:
--   In the setting of Lemma 5, let $\Delta=\sum_{\text{greedy}}\alpha_i(t-t_i)$, let $r$ be the number of positive $\alpha_i$, $n$ the size of the original ground set, and $G=[r(n-1)-1](\beta-\Delta)$ the guard (6). If $\theta>0$, $\Delta<\beta$ and
--
--   $$L\ >\ 4N^2G+4N\beta, \tag{7}$$
--
--   then there is a block $z$ with $\theta c_z>G$, and its set $A_z$ is nonempty and a proper subset of $V(D)$.
--
--   The block $z$ is the target from which the next arc of the implication graph is extracted.
--
--   Differences from the source:
--   - generalization: certificate terms are stored greedy and graph vectors → any vectors with the bounds of Lemma 5's hypotheses; reason: as in Lemma 5
--   - generalization: the quotient DAG of the implication graph (SCCs contracted) → any partition of Fin n into N nonempty blocks with an acyclic arc relation on the blocks; reason: the lemma's proof uses only these properties (reading R8); the quotient DAG is one instance
--   - reading: the algorithm's standing setting (h(∅), h(U) ≥ m, so that H_t is submodular, p.9) → explicit hypothesis EndpointsAbove h t: h(∅) + 1 − t ≤ h(∅) and h(∅) + 1 − t ≤ h(U); reason: reading R7: the algorithm's context made explicit
--   - encoding: A_z is "a proper subset of the ground set" → A_z ≠ V(D) (the block set); reason: A_z is a set of blocks; its ground set is V(D)
--   - generalization: 0 ≤ ∆ < β in (6) (timestamps t_i ≤ t of the algorithm) → arbitrary timestamps; only ∆ < β is assumed; reason: the proof uses only β − ∆ > 0; in the algorithm ∆ ≥ 0, so the source's case is an instance
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 6, eqs. (6)–(7), p.13

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_BlockDAG

namespace FasterSFM

open Classical

/-- **Lemma 6** (A block containing the head of a new arc), p.13.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 6, eqs. (6)–(7), p.13.

"If θ > 0, ∆ < β, and L > 4N²G + 4Nβ, (7) there is a block z with θc_z > G. Its A_z is nonempty and
a proper subset of the ground set."

In the setting of Lemma 5 (a certificate on a calibrated current DAG with `N` blocks), with
`∆ = Σ_{greedy} α_i (t − t_i)`, `r` the number of `α_i > 0`, and the guard (6)
`G = [r(n − 1) − 1](β − ∆)` with `n` the size of the original ground set.

**Formalization Note.** "Proper subset of the ground set" is `A_z ≠ V(D)` (the ground set of the
quotient DAG). Readings R7 (`EndpointsAbove h t`) and R8 (any block structure with acyclic arcs) as
in Lemma 5; the certificate hypotheses are those of Lemma 5 (generalization, as there). -/
theorem lemma_6 {n N m : ℕ} (h : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (D : BlockDAG n N) (t : ℝ) (hend : EndpointsAbove h t) (hcal : D.Calibrated h t)
    (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) (grd : Fin m → Bool) (stamp : Fin m → ℝ)
    (hcert : IsCertificate D h t a α grd)
    (hθ : 0 < certTheta α grd) (hΔ : certDelta α grd stamp t < certBeta a α)
    (h7 : 4 * (N : ℝ) ^ 2 * guardG n (certSupp α) (certBeta a α) (certDelta α grd stamp t) +
      4 * (N : ℝ) * certBeta a α < certL a α) :
    ∃ z : Fin N,
      guardG n (certSupp α) (certBeta a α) (certDelta α grd stamp t) < certTheta α grd * D.cz h t z ∧
      (D.A z).Nonempty ∧ D.A z ≠ Finset.univ := by sorry

end FasterSFM
