-- Prove2me | Theorems.Thm_DynHaussler_eq_107
-- name    : DynHaussler.eq_107
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:09.71849+00:00
-- url     : https://prove2.me/theorems/cd6b94ec-48d9-4917-a0d3-48117ae7992e
-- title:
--   Eq. (107) — $|H_q|=q(q^d-1)/(q-1)=q\sum_{j<d}q^j\ge q^d$
-- statement:
--   Let $\mathbb F_q$ be a field with $q$ elements and $d\ge1$, and let $H_q$ be the class of hyperplane indicators $h_{a,b}(x)=\mathbf 1\{a\cdot x=b\}$, $a\in\mathbb F_q^d\setminus\{0\}$, $b\in\mathbb F_q$, on $\mathbb F_q^d$ (Eq. (106)). Each distinct hyperplane has exactly $q-1$ parameter representations, and
--   $$
--   |H_q|=\frac{q(q^d-1)}{q-1}=q\sum_{j=0}^{d-1}q^j\ge q^d. \tag{107}
--   $$
--
--   This count supplies the $q^d$ pairwise separated traces behind the lower bound (119).
--
--   **Formalization Note** The field is any finite field and $q$ its cardinality. The cardinality of $H_q$ is shown to be a natural number $N$, and the quotient is stated as $N(q-1)=q(q^d-1)$.
--
--   Differences from the source:
--   - encoding: |H_q| = q(q^d − 1)/(q − 1) → encard H_q = N with N (q − 1) = q (q^d − 1) in ℕ; reason: q ≥ 2, so the equation is equivalent to the quotient
--   - encoding: a prime power q ≥ 2 and a field F_q with q elements → any finite field F, q = card F; reason: the cardinality of a finite field is a prime power ≥ 2, and every prime power is one
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (107), p.46 (PDF p.48)

import Mathlib
import Definitions.Def_DynHaussler_hypClass

set_option autoImplicit false

namespace DynHaussler

/-- **Eq. (107) (number of finite-field hyperplanes).** Let `F_q` be a field with `q` elements and
`d ≥ 1`. Each distinct hyperplane has exactly `q − 1` parameter representations, and the class
`H_q` of hyperplane indicators `1{a · x = b}` (`a ∈ F_q^d ∖ {0}`, `b ∈ F_q`) on `F_q^d` has
`|H_q| = q(q^d − 1)/(q − 1) = q ∑_{j=0}^{d−1} q^j ≥ q^d`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (107), p.46 (PDF p.48).

**Formalization Note** `F` is any finite field and `q = Fintype.card F` (automatically a prime
power `≥ 2`). `|H_q|` is the extended cardinality `Set.encard` of the set of distinct indicators, and
the statement says it is a natural number `N`; the quotient `q(q^d − 1)/(q − 1)` is stated as
`N (q − 1) = q (q^d − 1)` in `ℕ` (here `q − 1 ≥ 1` and `q^d − 1 ≥ 0`, so no subtraction truncates). -/
theorem eq_107 (F : Type*) [Field F] [Fintype F] (d : ℕ) (hd : 1 ≤ d) :
    ∃ N : ℕ, (hypClass F d).encard = N ∧
      N * (Fintype.card F - 1) = Fintype.card F * (Fintype.card F ^ d - 1) ∧
      N = Fintype.card F * ∑ j ∈ Finset.range d, Fintype.card F ^ j ∧
      Fintype.card F ^ d ≤ N := by sorry

end DynHaussler
