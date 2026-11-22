-- Prove2me | Theorems.Thm_Bernstein_addSubgroups
-- name    : Bernstein.addSubgroups
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:13:42.245175+00:00
-- url     : https://prove2.me/theorems/d3fe310d-f65e-4bfb-9b58-26e50edfa2f5
-- title:
--   Appendix A — three subgroups of E(F_{p²})
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer with $A^2 - 4$ not a square modulo $p$. Each of the following sets is a subgroup of $E(\mathbf{F}_{p^2})$:
--   - $\{\infty, (0, 0)\}$;
--   - $\{\infty\} \cup (E(\mathbf{F}_{p^2}) \cap (\mathbf{F}_p \times \mathbf{F}_p))$;
--   - $\{\infty\} \cup (E(\mathbf{F}_{p^2}) \cap (\mathbf{F}_p \times \sqrt{\delta}\,\mathbf{F}_p))$, for each $\sqrt{\delta} \in \mathbf{F}_{p^2}$ whose square is $\delta$, the smallest non-square in $\{1, \ldots, p - 1\}$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 20, Appendix A, the three subgroups of E(F_{p²})

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem addSubgroups (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∃ H : AddSubgroup (Pt p A),
      (H : Set (Pt p A)) =
        {Q | Q = 0 ∨ ∃ h : (Ecurve p A).Nonsingular 0 0, Q = .some 0 0 h}) ∧
    (∃ H : AddSubgroup (Pt p A), (H : Set (Pt p A)) = fpPoints p A) ∧
    (∀ s : Fp2 p, s ^ 2 = emb p (delta p : ZMod p) →
      ∃ H : AddSubgroup (Pt p A), (H : Set (Pt p A)) = twistPoints p A s) := by
  sorry

end Bernstein
