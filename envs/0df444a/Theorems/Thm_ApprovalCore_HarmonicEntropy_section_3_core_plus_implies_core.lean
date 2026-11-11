-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_section_3_core_plus_implies_core
-- name    : ApprovalCore.HarmonicEntropy.section_3_core_plus_implies_core
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:22.633645+00:00
-- url     : https://prove2.me/theorems/bdd645a9-9826-48fb-8bdd-32f7bddf9591
-- title:
--   §3 — core+ implies the core (binary $(y,z)$ recover the coalitions that block)
-- statement:
--   Throughout, the standing assumption of p. 4 is in force: $\frac{n}{k+1} < q \le \frac{n}{k}$.
--   Every committee $W \in \mathcal W$ that satisfies core+ at quota $q$ is in the core at quota $q$. Indeed, a blocking coalition $S$ with proposal $T$ gives the binary vectors $y = \mathbf 1_S \ne 0$ and $z = \mathbf 1_T$, and for each $i \in S$ the left-hand side of (2) equals $u_i(T)$, so (2) becomes (1); for $i \notin S$ it holds automatically, and affordability is $|S| \ge q|T|$.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 4 (PDF 5), §3, paragraph after Definition 3.1

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election

namespace ApprovalCore.HarmonicEntropy

/-- §3 (p. 4): binary `(y, z)` recover the ordinary coalitions that block, so a committee
satisfying core+ at quota `q` is in the core at quota `q`. -/
theorem section_3_core_plus_implies_core {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ))
    (W : Finset (Fin m)) (hW : SatisfiesCorePlus I q W) :
    InCore I q W := by sorry

end ApprovalCore.HarmonicEntropy
