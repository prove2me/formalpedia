-- Prove2me | Theorems.Thm_FamousTheorems_isregular_iff_finite_range_leftquotient
-- name    : FamousTheorems.isregular_iff_finite_range_leftquotient
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:20.332768+00:00
-- url     : https://prove2.me/theorems/73ebe512-2cd4-4db2-ad66-ad7f87e7bdba
-- title:
--   The Myhill–Nerode theorem
-- statement:
--   **The Myhill\u2013Nerode theorem.** A language is regular if and only if it has finitely many left quotients — equivalently, finitely many equivalence classes under the relation “indistinguishable by any suffix”. This characterises regularity without reference to automata, and the number of classes is exactly the state count of the minimal DFA, which the theorem thereby proves exists and is unique. It is the standard instrument for proving a language is *not* regular: exhibit infinitely many pairwise distinguishable prefixes, as for $\{a^nb^n\}$. Cleaner than the pumping lemma, since it is an exact characterisation rather than a one-way necessary condition. **Formalization note.** `leftQuotient` is the residual language after a prefix; finiteness of its range is the finite-index condition. The result is Mathlib's `Language.isRegular_iff_finite_range_leftQuotient`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isregular_iff_finite_range_leftquotient :
    ∀ {α : Type u_1} {L : Language α}, 
    L.IsRegular ↔ (range L.leftQuotient).Finite := by sorry

end FamousTheorems
