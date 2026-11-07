-- Prove2me | Theorems.Thm_DetCCHard_lemma_6_10
-- name    : DetCCHard.lemma_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:43.946228+00:00
-- url     : https://prove2.me/theorems/7a415e1c-9aee-4601-8acd-7b916b70e16c
-- title:
--   Lemma 6.10 — conditioning on an event of weight $v$ perturbs all 8-coordinate marginals outside $e(v,\tau)$ coordinates by at most $\varepsilon(v,\tau)$
-- statement:
--   Let $\nu$ be the normalized weights of an indexed exactly 8192-wise independent tuple list on $Z^q$ ($q \ge 1$, $Z$ finite) with marginal $\mu$, and let $0 < v, \tau \le 1$. For every event $Y$ of labels with $\nu(Y) \ge v$ there is a set $E \subseteq [q]$ with $|E| \le e(v, \tau)$ such that
--   $$
--   d_{\mathrm{TV}}\bigl((\nu \mid Y)_J,\ \mu_J\bigr) \le \varepsilon(v, \tau) \qquad (J \subseteq [q] \setminus E,\ |J| \le 8).
--   $$
--   Here total variation is the maximum absolute difference between the two distributions' probabilities of an event, and $\varepsilon(v,\tau) = \min\{\tau, 2^{-30} v^{1/256}\}$, $e(v,\tau) = 8\lceil 2^{20}\varepsilon(v,\tau)^{-2} v^{-1/512}\rceil$.
--
--   Independence survives conditioning on any heavy event, up to few exceptional coordinates; this is what lets the explicit lists replace full products.
--
--   **Formalization Note** Total variation is the published `MarkovMixing.tvDist`, $\max_A |P(A) - Q(A)|$ over events $A \subseteq Z^J$, the paper's definition.
--
--   Differences from the source:
--   - generalization: prescribed normalized (positive, §4.2) marginal weights μ on Z → any μ : Z → ℚ with which the list is exactly 8192-wise independent; reason: with q ≥ 1 exact independence forces μ(z) = ν(z(ℓ)_1 = z) ≥ 0 and ∑ μ = 1, a letter of weight zero is decoded by no label, and positive μ is a special case
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 6.10, p.26 (ε and e: display before the lemma)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_epsVT

namespace DetCCHard

/-- **Lemma 6.10 (Conditioning outside exceptional coordinates)** (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Lemma 6.10, p.26). Let `ν` be the normalized
weights of an indexed exactly 8192-wise independent tuple list on `Z^q` with marginal `μ`, and let
`0 < v, τ ≤ 1`. For every event `Y` of labels with `ν(Y) ≥ v` there is a set `E ⊆ [q]` with
`|E| ≤ e(v, τ)` such that `d_TV((ν | Y)_J, μ_J) ≤ ε(v, τ)` for every `J ⊆ [q] ∖ E` with
`|J| ≤ 8`.

**Formalization Note** Total variation is the published `MarkovMixing.tvDist`, the maximum over
events `A ⊆ Z^J` of `|P(A) − Q(A)|`, exactly the paper's definition ("the maximum absolute
difference between the two distributions' probabilities of an event"). `(ν | Y)_J` is
`condMarginal`, `μ_J` is `prodMarginal`; `ε(v, τ)` and `e(v, τ)` are `epsVT` and `eVT`. The
alphabet is finite with decidable equality; coordinates are `Fin q`, `q ≥ 1`. -/
theorem lemma_6_10 {Z : Type} [Fintype Z] [DecidableEq Z] {q : ℕ} (hq : 1 ≤ q)
    (T : TupleList Z (Fin q)) (μ : Z → ℚ) (hT : ExactlyIndep T 8192 μ) (v τ : ℝ) (hv0 : 0 < v)
    (hv1 : v ≤ 1) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (Yev : Set T.L) (hY : v ≤ (wt T.ν Yev : ℝ)) :
    ∃ E : Finset (Fin q), E.card ≤ eVT v τ ∧
      ∀ J : Finset (Fin q), Disjoint J E → J.card ≤ 8 →
        MarkovMixing.tvDist (condMarginal T.ν T.z Yev J) (prodMarginal μ J) ≤ epsVT v τ := by sorry

end DetCCHard
