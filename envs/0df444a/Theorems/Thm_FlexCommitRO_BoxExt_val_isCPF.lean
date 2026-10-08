-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_val_isCPF
-- name    : FlexCommitRO.BoxExt.val_isCPF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:33.168674+00:00
-- url     : https://prove2.me/theorems/469d60b5-9ae8-47c3-a0e5-5f9b3096154b
-- title:
--   Proof of Lemma 2, p. 270 — val(b) = min{f(s) : As ≥ b, ‖s‖∞ ≤ R} is a c.p.f. of b when f is
-- statement:
--   Let $f : \mathbb R^m \to \mathbb R \cup \{+\infty\}$ be a convex polyhedral function, $A \in \mathbb R^{k \times m}$ and $R \in \mathbb R$. Define, for $b \in \mathbb R^k$,
--   $$
--   \operatorname{val}(b) = \inf\{ f(s) : As \ge b,\ \|s\|_\infty \le R \} \in [-\infty, +\infty]
--   $$
--   (equal to $+\infty$ when the constraint set is empty). Then $\operatorname{val}$ is a convex polyhedral function of $b$.
--
--   The paper calls this "well known"; it makes the value of the last-stage problem of the worst-case dynamic program again a c.p.f., so that the induction in Lemma 2 stays in the class of c.p.f.s.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2 ("The following result is well known")

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem val_isCPF {m k : ℕ} (f : (Fin m → ℝ) → EReal) (hf : IsCPF f)
    (A : Matrix (Fin k) (Fin m) ℝ) (R : ℝ) :
    IsCPF (fun bv : Fin k → ℝ => ⨅ s ∈ {s : Fin m → ℝ | bv ≤ A *ᵥ s ∧ ‖s‖ ≤ R}, f s) := by sorry

end FlexCommitRO.BoxExt
