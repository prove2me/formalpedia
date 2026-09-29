-- Prove2me | Theorems.Thm_FiniteAbelianGroups_card_pow_eq_le_card_ker
-- name    : FiniteAbelianGroups.card_pow_eq_le_card_ker
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:13:21.094895+00:00
-- url     : https://prove2.me/theorems/998608cb-ff5f-4031-987d-6c39b2670ab1
-- title:
--   Fibres of the $k$-th power map are bounded by its kernel
-- statement:
--   **Every fibre of the $k$-th power map is bounded by the kernel.**
--
--   Let $G$ be a finite abelian group and $k \ge 0$. For any $a \in G$,
--
--   $$\#\{x \in G : x^{k} = a\} \;\le\; \bigl|\ker(x \mapsto x^{k})\bigr| .$$
--
--   Because $G$ is abelian, $x \mapsto x^{k}$ is a group homomorphism, so its fibres are either
--   empty or cosets of its kernel. A coset has the same cardinality as the kernel, which gives the
--   bound, with equality precisely when $a$ lies in the image, i.e. when $a$ is a $k$-th power.
--
--   This is the general form of the count; in the cyclic case the kernel has order exactly
--   $\gcd(k,|G|)$, and for a general finite abelian group it is the product of the corresponding
--   gcd's over the invariant factors. Statements of this shape are what let one count solutions of
--   $x^k = a$ uniformly, for instance in $(\mathbb{Z}/m)^\times$ for composite $m$, where the group
--   is a product of cyclic factors.
--
--   **Formalization note.** `powMonoidHom k` is Mathlib's $k$-th power homomorphism, available
--   because `G` is commutative; the solution set is a `Finset.filter` and the kernel is measured
--   with `Nat.card`.
-- source:
--   Classical; see Lang, *Algebra*, Ch. I. Lean proof extracted from `Salt/Maynard/PpRootTwo.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace FiniteAbelianGroups

theorem card_pow_eq_le_card_ker {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) (a : G) :
    (Finset.univ.filter (fun x : G => x ^ k = a)).card
      ≤ Nat.card (powMonoidHom k : G →* G).ker := by sorry

end FiniteAbelianGroups
