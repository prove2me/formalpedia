-- Prove2me | Theorems.Thm_ErschlerZheng_orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq
-- name    : ErschlerZheng.orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:03:53.272325+00:00
-- url     : https://prove2.me/theorems/407877ac-caa9-4735-bc30-3d651039d391
-- title:
--   p. 34 — the unlabelled Schreier graph of 1^∞, and hence its graph distance d_𝒮, does not depend on ω
-- statement:
--   For all strings $\omega, \omega' \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$:
--
--   1. the orbits of $1^\infty$ agree, $1^\infty \cdot G_\omega = 1^\infty \cdot G_{\omega'}$ (`orbitOne`);
--   2. every point $x$ of $1^\infty \cdot G_\omega$ has the same neighbours: for every ray $y$, $y = x \cdot s$ for some $s \in \{a, b_\omega, c_\omega, d_\omega\}$ if and only if $y = x \cdot s'$ for some $s' \in \{a, b_{\omega'}, c_{\omega'}, d_{\omega'}\}$ (`gens`);
--   3. every point $x$ of $1^\infty \cdot G_\omega$ has the same number of edges to each ray $y$: the number of the four labels $s = a, b_\omega, c_\omega, d_\omega$ with $y = x \cdot s$ equals the number of the labels $a, b_{\omega'}, c_{\omega'}, d_{\omega'}$ with that property;
--   4. for $x, y \in 1^\infty \cdot G_\omega$, $d_{\mathcal S_\omega}(x, y) = d_{\mathcal S_{\omega'}}(x, y)$ (`schreierDist`).
--
--   Conjunct 2 compares neighbours as a set; conjunct 3 counts the edges of the Schreier graph of p. 34, one for each label, so that a loop at $x$ is counted once for each generator fixing $x$.
--
--   Erschler and Zheng, p. 34: “Let $d_{\mathcal S_\omega}$ denote the graph distance on the Schreier graph $\mathcal S_\omega$. Because the unlabelled Schreier graph of $o$ does not depend on the sequence $\omega$, it follows that the graph distance also doesn’t depend on $\omega$. For this reason we can omit reference to $\omega$ and write $d_{\mathcal S}$ for the graph distance.”
--
--   Conjuncts 1 to 3 are “the unlabelled Schreier graph of $o$ does not depend on the sequence $\omega$”: the vertices, and the edges both as a set of neighbours and with their multiplicities, the graph of p. 34 having an edge from $x$ to $x \cdot s$ for each generator $s$. Conjunct 4 is its consequence for the distance.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 34, the Schreier graph does not depend on ω

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq (ω ω' : ℕ → Fin 3) :
    orbitOne ω = orbitOne ω' ∧
      (∀ x ∈ orbitOne ω, ∀ y : Ray, (∃ s ∈ gens ω, y = x <• s) ↔ ∃ s ∈ gens ω', y = x <• s) ∧
      (∀ x ∈ orbitOne ω, ∀ y : Ray,
        Nat.card {i : Fin 4 // y = x <• ![Garrido.grigA, gen ω .b, gen ω .c, gen ω .d] i} =
          Nat.card {i : Fin 4 // y = x <• ![Garrido.grigA, gen ω' .b, gen ω' .c, gen ω' .d] i}) ∧
      ∀ x ∈ orbitOne ω, ∀ y ∈ orbitOne ω, schreierDist ω x y = schreierDist ω' x y := by
  sorry

end ErschlerZheng
