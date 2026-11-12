-- Prove2me | Theorems.Thm_BFFPyramidal_multiplicity_bound
-- name    : BFFPyramidal.multiplicity_bound
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:28:54.671997+00:00
-- url     : https://prove2.me/theorems/1b8d6e3d-6b36-4f8e-b79a-9885fa9543b0
-- title:
--   Multiplicity of a coset partition of a pyramidal group
-- statement:
--   **Main theorem (Berger-Felzenbaum-Fraenkel).** Let $G$ be a pyramidal group and suppose the cosets $a_iK_i$, $1 \le i \le t$, with $K_i \le G$ and $a_i \in G$, partition $G$. If $t > 1$, then at least
--   $$ x \;=\; \left\lfloor \frac{P(l)\,\varphi(l)}{l} \right\rfloor + 1 $$
--   of the subgroups $K_i$ have the same order, where
--   $$ l \;=\; \frac{|G|}{\gcd\!\left(|K_1|,\dots,|K_t|\right)}, $$
--   $P$ is the greatest prime factor and $\varphi$ is Euler's totient function.
--
--   Since $x \ge 2$ for $l \ge 2$, this proves the conjectures of Herzog-Schönheim and of Burshtein for pyramidal groups; the authors had previously established the Herzog-Schönheim conjecture for finite nilpotent groups, which form a subclass.
--
--   **Formalization note.** The conclusion is stated as the existence of an order $m$ such that the number of indices $i$ with $|K_i| = m$ is at least $x$; counting indices (not distinct subgroups) is the faithful reading, since several $K_i$ may coincide. The floor is natural-number division. The hypothesis $t > 1$ is necessary: for $t = 1$ the partition is $G$ itself, $l = 1$, and the bound degenerates.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 139, THEOREM with eqs. (3)-(4)

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_arithmetic
import Definitions.Def_BFFPyramidal_cosetPartition

namespace BFFPyramidal

theorem multiplicity_bound {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (ht : 1 < t) (K : Fin t → Subgroup G) (a : Fin t → G)
    (hpart : IsCosetPartition K a) :
    ∃ m : ℕ, (maxPrimeFac (modulus K) * Nat.totient (modulus K)) / modulus K + 1
      ≤ (Finset.univ.filter fun i => Nat.card (K i) = m).card := by
  sorry

end BFFPyramidal
