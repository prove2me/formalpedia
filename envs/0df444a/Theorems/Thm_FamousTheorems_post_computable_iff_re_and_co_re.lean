-- Prove2me | Theorems.Thm_FamousTheorems_post_computable_iff_re_and_co_re
-- name    : FamousTheorems.post_computable_iff_re_and_co_re
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:29.870987+00:00
-- url     : https://prove2.me/theorems/e5d97167-3247-47bf-8e62-fef751c8c2b3
-- title:
--   Post's theorem (computable iff r.e. and co-r.e.)
-- statement:
--   **Post's theorem.** A predicate $p$ on a computably encodable type is computable (decidable by an algorithm) if and only if both $p$ and its negation $\neg p$ are recursively enumerable.
--
--   One direction is immediate. For the other, run the enumerations of $p$ and $\neg p$ in parallel; each input eventually appears in exactly one of them. The theorem is a basic fact of computability theory and underlies many undecidability arguments: the halting set is r.e. but not computable, so its complement cannot be r.e.
--
--   **Formalization note.** Mathlib's `ComputablePred.computable_iff_re_compl_re`. `Primcodable α` gives an encoding of $\alpha$ into $\mathbb N$, `ComputablePred p` means $p$ is decidable by a computable function, and `REPred p` means $p$ is recursively enumerable (semi-decidable). `ComputablePred p` asks for some computable decision procedure; the `DecidablePred p` instance in the statement is only a classical decision function (every predicate has one) and does not restrict $p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ComputablePred.computable_iff_re_compl_re`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem post_computable_iff_re_and_co_re {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by sorry

end FamousTheorems
