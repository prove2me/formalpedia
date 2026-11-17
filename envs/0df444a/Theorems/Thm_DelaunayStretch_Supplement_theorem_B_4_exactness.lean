-- Prove2me | Theorems.Thm_DelaunayStretch_Supplement_theorem_B_4_exactness
-- name    : DelaunayStretch.Supplement.theorem_B_4_exactness
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:39:17.014057+00:00
-- url     : https://prove2.me/theorems/c0475c33-32bc-4dda-baab-54b30d8ca029
-- title:
--   Theorem B.4 (Exactness) — for $U\ge\pi/2$ the chain inequality holds iff a feasible potential exists, and then $W^*_U$ is the smallest one and solves (B.1)
-- statement:
--   Let $U\ge\pi/2$. Then:
--
--   1. the chain inequality holds at level $U$ (every disk chain satisfies $P(u,v)\le U\|u-v\|$) if and only if there is a feasible potential of level $U$.
--
--   Suppose now that the chain inequality holds at level $U$. Then:
--
--   2. the value function $W^*_U$ is finite at every gate state;
--   3. for every gate state $s=(O,G,\delta)$ it satisfies the dynamic programming equation
--
--   $$
--   W^*_U(s)=\max\Bigl(\kappa-U\bigl(x(w_+(O))-x(c(s))\bigr),\ \sup_{O'}\bigl[\Delta\mu-U\,\Delta x+W^*_U(s')\bigr]\Bigr),\tag{B.1}
--   $$
--
--      where $\kappa$ is the cost of the final step at $s$, the supremum is over all next disks $O'$ for $s$, and $\Delta\mu$, $\Delta x$ and $s'$ are the cost, the progress and the gate state of the step from $s$ to $O'$;
--   4. $W^*_U$ is a feasible potential of level $U$;
--   5. $W^*_U\le W$ at every gate state, for every feasible potential $W$ of level $U$.
--
--   The "if" direction of item 1 is Theorem 3.9; the theorem shows that the potential criterion loses nothing, and the claims 2–5 are Proposition 3.8. Equation (B.1) says that a best continuation from $s$ either ends with the final step at once or takes one step and then continues optimally.
--
--   **Formalization Note** $W^*_U$ takes values in the extended reals; "finite" means equal to a real number. The supremum in (B.1) is the extended-real supremum over next disks together with their new gate ends (determined by (N1)), and equals $-\infty$ when $s$ has no next disk, in which case the maximum is the final-step term. Feasibility is asserted for the real-valued function $s\mapsto W^*_U(s)$ (converted to a real number), which agrees with $W^*_U$ at every gate state; the inequalities of a feasible potential only evaluate it at gate states.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im; reason: ℂ is ℝ² with the Euclidean norm; same instances (the base mission's convention)
--   - encoding: W*_U(s) ∈ (−∞, +∞] → an EReal-valued function; "finite at every gate state" → equal to a real number at every gate state; reason: EReal contains (−∞, +∞]; same values
--   - encoding: the supremum in (B.1) over next disks O′ → the EReal supremum over O′ and its new gate ends a′, b′ with IsNextDisk s O′ a′ b′ (⊥ for no next disk); reason: (N1) determines a′, b′ from O and O′, and the empty supremum is absorbed by the max with a real term; same values
--   - encoding: W*_U is a feasible potential → the real-valued function s ↦ (W*_U s).toReal is a feasible potential; reason: by the finiteness clause it equals W*_U at every gate state, and a feasible potential is only evaluated at gate states (initial pairs and steps lead to gate states)
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem B.4, pp.54–55 (equation (B.1), p.54); its W*_U part is Proposition 3.8, pp.19–20

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsFeasiblePotential
import Definitions.Def_DelaunayStretch_Supplement_valueFunction

namespace DelaunayStretch.Supplement

/-- **Theorem B.4 (Exactness)** (pp.54–55). Let `U ≥ π/2`. Then the chain inequality holds at
level `U` if and only if there is a feasible potential of level `U`. In this case, the value
function `W*_U` is finite at every gate state and satisfies the dynamic programming equation (B.1)
`W*_U(s) = max(κ − U(x(w₊(O)) − x(c(s))), sup_{O′} (Δµ − U Δx + W*_U(s′)))` for every gate
state `s = (O, G, δ)`, where the supremum is over all next disks `O′` for `s`; moreover `W*_U` is
a feasible potential of level `U`, and `W*_U ≤ W` for every feasible potential `W` of level `U`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem B.4,
pp.54–55.

**Formalization Note** `W*_U` is `valueFunction U`, with values in `EReal`; "finite" is
`∃ r : ℝ, W*_U s = r`. The supremum in (B.1) ranges over next disks `O′` with their new gate ends
`a′, b′` (determined by (N1)); it is the `EReal` supremum, `⊥` when `s` has no next disk. The
feasibility claim is stated for the real-valued function `s ↦ (W*_U s).toReal`, which agrees
with `W*_U` at every gate state; a feasible potential only reads its values at gate states (every
initial pair and every step leads to one). -/
theorem theorem_B_4_exactness (U : ℝ) (hU : Real.pi / 2 ≤ U) :
    (ChainInequality U ↔ ∃ W : GateState → ℝ, IsFeasiblePotential U W) ∧
    (ChainInequality U →
      (∀ s : GateState, s.IsGateState → ∃ r : ℝ, valueFunction U s = (r : EReal)) ∧
      (∀ s : GateState, s.IsGateState →
        valueFunction U s =
          max ((finalCost s - U * finalProgress s : ℝ) : EReal)
            (⨆ (O' : Disk) (a' : ℂ) (b' : ℂ) (_ : IsNextDisk s O' a' b'),
              ((stepCost s a' b' - U * stepProgress s a' b' : ℝ) : EReal) +
                valueFunction U (stepState s O' a' b'))) ∧
      IsFeasiblePotential U (fun s => (valueFunction U s).toReal) ∧
      (∀ W : GateState → ℝ, IsFeasiblePotential U W →
        ∀ s : GateState, s.IsGateState → valueFunction U s ≤ (W s : EReal))) := by sorry

end DelaunayStretch.Supplement
