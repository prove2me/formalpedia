-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_lemma_2
-- name    : CapacityRights.Gatekeeper.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:57.596282+00:00
-- url     : https://prove2.me/theorems/6c36a622-2b10-49ab-b71c-7d4644450f60
-- title:
--   Lemma 2: unique efficient fungible capacity from expected shadow price
-- statement:
--   In a stationary environment with fungible capacity, a positive capacity $k$ maximizes the firm's net present value if and only if its expected shadow price equals the user cost of capacity:
--
--   $$
--   \mathbb E_{\tilde\epsilon}[S(k\mid w,\tilde\epsilon)]=c,
--   \qquad c=\frac{v}{\sum_{t=1}^{T}\gamma^t}.
--   $$
--
--   At most one positive capacity satisfies this equation. Thus, when an interior efficient capacity exists, the expected marginal value of fungible capacity characterizes it uniquely.
--
--   **Formalization Note** Footnote 18 makes the positive-capacity condition explicit. Efficient capacity is defined by global maximization of net present value, not by this equation. Strict concavity and regularity are in the shared standing assumptions.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 19 (PDF 22), Lemma 2, equations (13)–(14) and footnote 18

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Lemma 2, p. 19 (PDF 22), with its nonzero-capacity footnote. -/
theorem lemma_2 (E : Env) (hS : E.Standing) :
    (∀ k : ℝ, 0 < k →
      (IsEfficient E k ↔ (∫ e, S E k e ∂E.μ) = ucc E)) ∧
    (∀ k1 k2 : ℝ, 0 < k1 → 0 < k2 →
      (∫ e, S E k1 e ∂E.μ) = ucc E →
      (∫ e, S E k2 e ∂E.μ) = ucc E → k1 = k2) := by sorry

end CapacityRights.Gatekeeper
