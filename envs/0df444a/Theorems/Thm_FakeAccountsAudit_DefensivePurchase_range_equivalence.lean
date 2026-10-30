-- Prove2me | Theorems.Thm_FakeAccountsAudit_DefensivePurchase_range_equivalence
-- name    : FakeAccountsAudit.DefensivePurchase.range_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:44:45.840128+00:00
-- url     : https://prove2.me/theorems/e3782d53-6a7f-4a14-ad94-07784d963fec
-- title:
--   (16) ↔ (19) — equivalent effort and price thresholds
-- statement:
--   Let $P$ be the published parameter record, let $\tau<1$ and $l>0$, and let $d\in\mathbb R$. Define the unit fake-account price, revenue threshold and effort threshold by
--
--   $$
--   p_f(d)=p_0+\frac{d}{1-\tau},\qquad
--   \eta_2=\frac{\lambda_i\mu(1-l^2)}{l},\qquad
--   d_2=(1-\tau)(\eta_2-p_0).
--   $$
--
--   Then the effort condition (16) and price condition (19) are equivalent:
--
--   $$d\le d_2\quad\Longleftrightarrow\quad p_f(d)\le\eta_2.$$
--
--   This is the range conversion delimiting the paper's conditional costly separating branch. It is not the existence, belief construction or uniqueness claim of Lemma 2. On economic instances the effort is nonnegative, the technology lies in $[0,1)$ and all of the source's standing assumptions still govern the game. The algebraic equivalence also holds at every real effort with the stated positive denominator and places no restrictions on the unused coordinates.
--
--
--   Differences from the source:
--   - generalization: the nonnegative effort and standing parameter domain of §3 and §4.2.2 → every real effort and every raw parameter record with τ<1 and l>0; reason: the equivalence only rearranges the affine price with positive slope; every source-admissible instance satisfies these conditions
--   - encoding: the thresholds and price in (16) and (19) → the published real-valued price, eta2 and d2 functions, with l>0 explicit; reason: the same formulas are used and division by the literacy parameter is confined to its defined domain
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8872, §4.2.2, equations (16) and (19), PDF page 9; DOI:10.1287/mnsc.2022.02616

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting
set_option autoImplicit false

namespace FakeAccountsAudit.DefensivePurchase

/-- Huang--Liu, p. 8872 (PDF 9), (16) iff (19). Algebraic range conversion,
not Lemma 2's equilibrium existence or uniqueness assertion. The rearrangement
extends to every real effort and unrestricted unused parameter coordinates. -/
theorem range_equivalence (P : FakeAccounts.Platform.Params)
    (htau : P.tau < 1) (hl : 0 < P.l) (d : ℝ) :
    d ≤ FakeAccounts.Platform.d2 P ↔
      FakeAccounts.Platform.price P d ≤ FakeAccounts.Platform.eta2 P := by sorry

end FakeAccountsAudit.DefensivePurchase
