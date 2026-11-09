-- Prove2me | Theorems.Thm_DepthOneQExp_theorem_2_3
-- name    : DepthOneQExp.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:44.759799+00:00
-- url     : https://prove2.me/theorems/84eafeea-7caa-452d-8950-adc88071a01d
-- title:
--   Theorem 2.3: $\|\frac1{14}\sum_{i=3}^{16}\rho(U_i) - \mathbb E_P\rho(P)\| \le 1 - 1/(48\cdot 10^5)$ for every representation of $G_{3s}$
-- statement:
--   For every integer $s\ge1$, let $U_3,\dots,U_{16}$ be the unitaries of Theorem 2.2, viewed as elements of the CNOT group $G_{3s}$. Then for every finite-dimensional unitary representation $\rho$ of $G_{3s}$,
--   $$
--   \Big\|\frac1{14}\sum_{i=3}^{16}\rho(U_i) - \mathbb E_{P\sim\mu(G_{3s})}\rho(P)\Big\| \le 1-\frac1{48\cdot10^5}.
--   $$
--
--   The bound is uniform in $s$ and in $\rho$: the fourteen depth-1 CNOT circuits form an expanding generating set of $G_{3s}$ in every representation. Applied to $P\mapsto P\otimes P$ it supplies the hypothesis of Theorem 2.13.
--
--   **Formalization Note** $\mu(G_{3s})$ is the uniform distribution, so the expectation is the finite average; the norm is the Euclidean operator norm.
--
--   Differences from the source:
--   - encoding: E_{P∼µ(G_{3s})} ρ(P) → (1/|G_{3s}|) Σ_{P ∈ G_{3s}} ρ(P); reason: µ is the uniform distribution on the finite group
--   - encoding: U_3, …, U_16 as unitary matrices → the elements cnotU s of G_{3s} whose permutation matrices are U_3, …, U_16; reason: ρ is a representation of G_{3s}, so the U_i enter as group elements; same objects
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.3, Eq. (2.13), p.8

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotU

namespace DepthOneQExp

/-- Theorem 2.3 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.3, Eq. (2.13),
p.8): for every integer `s ≥ 1` and every finite-dimensional unitary representation `ρ` of `G_{3s}`,
`‖(1/14) Σ_{i=3}^{16} ρ(U_i) − E_{P∼µ(G_{3s})} ρ(P)‖ ≤ 1 − 1/(48·10⁵)`.

**Formalization Note** `U_3, …, U_16` are the elements `cnotU s` of `G_{3s}`; `µ(G_{3s})` is the
uniform distribution, so the expectation is the finite average. The norm is the Euclidean operator
norm `ConstGapCircuits.opNorm`. -/
theorem theorem_2_3 (s : ℕ) (hs : 1 ≤ s) (ρ : ConstGapCircuits.UnitaryRep (cnotGroup (3 * s))) :
    ConstGapCircuits.opNorm
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (cnotU s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
          (1 / (Fintype.card (cnotGroup (3 * s)) : ℂ)) •
            ∑ P : cnotGroup (3 * s), (ρ.hom P : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) ≤
      1 - 1 / (48 * 10 ^ 5) := by sorry

end DepthOneQExp
