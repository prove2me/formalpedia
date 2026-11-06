-- Prove2me | Theorems.Thm_FasterSFM_lemma_5
-- name    : FasterSFM.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:33.802394+00:00
-- url     : https://prove2.me/theorems/1b108d7b-ed29-4f52-9e4d-5a072048e7bc
-- title:
--   Lemma 5 — acyclic no-cancellation: $L\le4N\theta c+4N\beta$
-- statement:
--   Let $h$ be submodular, let the current DAG $D$ with $N$ blocks be calibrated at $t$, with $h(\emptyset),h(U)\ge h(\emptyset)+1-t$, and let $c=\sum_z c_z$ with $c_z=H_t(A_z)$. Let $(\alpha_i,a_i)$ be a certificate: a convex combination of nonzero vectors on the blocks, each summing to $0$, where every greedy term satisfies $a_i(X)\le H_t(X)$ on proper nonempty closed sets and every graph term satisfies $a_i(X)\le0$ on closed sets. Then
--
--   $$L\ \le\ 4N\theta c+4N\beta, \tag{5}$$
--
--   with $L=\sum_i\alpha_i\|a_i\|_1$, $\theta=\sum_{\text{greedy}}\alpha_i$ and $\beta=\tfrac12\|y\|_1$, $y=\sum_i\alpha_ia_i$.
--
--   The inequality says that a certificate cannot cancel to a short vector unless some calibration value is large, which is what produces new arcs.
--
--   Differences from the source:
--   - generalization: certificate terms are stored greedy and graph vectors → any vectors summing to 0 with a_i(X) ≤ H_t(X) (greedy) on proper nonempty closed X and a_i(X) ≤ 0 (graph) on closed X; reason: Lemma 4 gives these bounds for stored vectors; the proof uses nothing else
--   - generalization: the quotient DAG of the implication graph (SCCs contracted) → any partition of Fin n into N nonempty blocks with an acyclic arc relation on the blocks; reason: the lemma's proof uses only these properties (reading R8); the quotient DAG is one instance
--   - reading: the algorithm's standing setting (h(∅), h(U) ≥ m, so that H_t is submodular, p.9) → explicit hypothesis EndpointsAbove h t: h(∅) + 1 − t ≤ h(∅) and h(∅) + 1 − t ≤ h(U); reason: reading R7: the algorithm's context made explicit
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 5, eq. (5), p.13

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_BlockDAG

namespace FasterSFM

open Classical

/-- **Lemma 5** (Acyclic no-cancellation), p.13.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 5, eq. (5), p.13.

"For a calibrated current DAG with N blocks and c = Σ_z c_z, L ≤ 4Nθc + 4Nβ. (5)"

Here `(α_i, a_i)` is a certificate (§4.3, p.12): a convex combination of nonzero vectors on the
blocks, each summing to `0`; greedy terms satisfy `a_i(X) ≤ H_t(X)` on proper nonempty closed sets,
graph terms `a_i(X) ≤ 0` on closed sets; `L = Σ α_i ‖a_i‖₁`, `β = Σ_v [−y_v]₊ = ‖y‖₁/2`,
`θ = Σ_{greedy} α_i`, `c_z = H_t(A_z)`.

**Formalization Note.**
* Generalization: the greedy terms are only assumed to satisfy `a_i(X) ≤ H_t(X)` on proper nonempty
  closed sets, which Lemma 4 gives for stored greedy vectors; any block structure with acyclic arcs
  (reading R8).
* Reading R7: `EndpointsAbove h t` (the witness value is at most `h(∅)`, `h(U)`), the algorithm's
  standing fact that makes `H_t` submodular. -/
theorem lemma_5 {n N m : ℕ} (h : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (D : BlockDAG n N) (t : ℝ) (hend : EndpointsAbove h t) (hcal : D.Calibrated h t)
    (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) (grd : Fin m → Bool)
    (hcert : IsCertificate D h t a α grd) :
    certL a α ≤ 4 * (N : ℝ) * certTheta α grd * (∑ z, D.cz h t z) + 4 * (N : ℝ) * certBeta a α := by sorry

end FasterSFM
