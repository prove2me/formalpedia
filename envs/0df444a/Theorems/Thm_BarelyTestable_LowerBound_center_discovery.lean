-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_center_discovery
-- name    : BarelyTestable.LowerBound.center_discovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:24:00.781861+00:00
-- url     : https://prove2.me/theorems/cc06de8f-9d94-4382-8ddc-67d02fa8ae13
-- title:
--   Lemma 3.19 — adaptive center-discovery bound
-- statement:
--   Fix a positive $m$, either sign, and any deterministic adaptive procedure $A$ that halts after at most $q$ queries for every real oracle. Under the corresponding hard law,
--
--   $$\Pr[A\text{ discovers a center}]\le q^2/2^m.$$
--
--   Discovery uses a slice-$01$ query supplying $Y$ and a slice-$11$ query supplying $X$ with $\alpha(X)=\beta(Y)$, regardless of their order and their other halves. Repeated queries are allowed, and $q$ is a worst-case bound.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - encoding: independent uniform labels and table entries → uniform counting probability on the full finite product Sample m; reason: every assignment occurs once, giving exactly the independent product law and its pushforward to the constructed real functions
--   - encoding: a deterministic algorithm making at most q queries → a history-based Procedure with Budget A q, and the actual run transcript; reason: every seed-fixed adaptive algorithm induces such a rule; query choices use only earlier exact real answers
--   - generalization: Lemma 3.19, under the standing assumption of §3 (p.11) that m is a large enough integer → every m ≥ 1; reason: the source proof uses no lower bound on m, and the Lean statement specializes to every large m
--   - encoding: sign σ ∈ {+1,−1} → a Boolean selecting +1 or −1; reason: both possible signs are quantified, with true selecting YES
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.19, p. 25 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Discovery

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.19, p.25: unrestricted query order and arbitrary deterministic adaptive rules. -/
theorem center_discovery {m : ℕ} (hm : 1 ≤ m) (A : Procedure (Coord m))
    (q : ℕ) (hbudget : Budget A q) (sign : Bool) :
    discoveryProbability A q sign ≤ (q : ℝ)^2 / 2^m := by sorry

end BarelyTestable.LowerBound
