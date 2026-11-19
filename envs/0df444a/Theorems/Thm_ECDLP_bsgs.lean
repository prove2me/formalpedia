-- Prove2me | Theorems.Thm_ECDLP_bsgs
-- name    : ECDLP.bsgs
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T23:45:23.81423+00:00
-- url     : https://prove2.me/theorems/88140d96-3ccf-4476-a611-d61e28e085c6
-- title:
--   Baby-step giant-step: existence of a match below $\sqrt{n}$
-- statement:
--   Let $G$ be an additive commutative group, $P \in G$ of order $n > 0$, and $Q = xP$ with $0 \le x < n$. Put $m = \lfloor\sqrt{n}\rfloor + 1$. Then there exist natural numbers $i, j < m$ such that
--
--   $$jP = Q - i(mP).$$
--
--   This is the correctness core of Shanks's **baby-step giant-step** method: writing $x = im + j$ with $i, j < m$, the baby step $jP$ matches the giant step $Q - i(mP)$, so a collision search over two lists of length $m = O(\sqrt{n})$ recovers $x = im + j$. For the challenge instance $m \approx 2^{127}$, which is why the method is infeasible there.
--
--   **Formalization Note.** `Nat.sqrt` is the integer square root; the bound $m = \lfloor\sqrt{n}\rfloor + 1$ ensures $m^2 > n$, so the quotient and remainder of $x$ by $m$ are both $< m$.
-- source:
--   Shanks, baby-step giant-step method (1971, unpublished); Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., Chapman & Hall/CRC 2008, §5.2.1, https://doi.org/10.1201/9781420071474.

import Mathlib

namespace ECDLP

theorem bsgs {G : Type*} [AddCommGroup G] {P Q : G} {n x : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) (hx : x < n) (hQ : Q = x • P) :
    let m := Nat.sqrt n + 1
    ∃ i j : ℕ, i < m ∧ j < m ∧ j • P = Q - i • (m • P) := by sorry

end ECDLP
