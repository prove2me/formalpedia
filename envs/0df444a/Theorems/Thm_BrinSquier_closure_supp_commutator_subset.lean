-- Prove2me | Theorems.Thm_BrinSquier_closure_supp_commutator_subset
-- name    : BrinSquier.closure_supp_commutator_subset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:40:16.491399+00:00
-- url     : https://prove2.me/theorems/cb1098e6-6b37-47f2-ad40-b1c1da244e8a
-- title:
--   The closure of a commutator's moved set stays inside the union of the moved sets
-- statement:
--   For piecewise-linear $f$ and $g$ with finitely many breakpoints, not merely the moved set of the commutator but its **closure** lies inside $\operatorname{supp} f \cup \operatorname{supp} g$:
--
--   $$\overline{\operatorname{supp}\, [f,g]} \ \subseteq\ \operatorname{supp} f \cup \operatorname{supp} g .$$
--
--   The inclusion without the closure is immediate, since a point fixed by both $f$ and $g$ is fixed by the commutator. The closure is the real content, and it is what rules out the commutator's moved set creeping up to the boundary.
--
--   A boundary point $t$ of $\operatorname{supp} f \cup \operatorname{supp} g$ is a *common fixed point* of $f$ and $g$. Brin-Squier's (2.14c) then gives an entire neighbourhood of $t$ on which the commutator is the identity — so that neighbourhood misses $\operatorname{supp}[f,g]$ entirely, and $t$ cannot be a limit of moved points.
--
--   **Role.** Together with (2.14b), which makes that closure compact, this is the statement that the set $W$ in the proof of (3.2) is nonempty: the commutator of a non-commuting pair is a non-identity element whose moved set has compact closure inside $\operatorname{supp} f \cup \operatorname{supp} g$. Every later step of that proof — the minimal component count, the confinement to a closed subinterval — is downstream of it.
--
--   **Formalization note.** The commutator is written left-associated as $f g f^{-1} g^{-1}$, and composition follows Mathlib's convention $(f \cdot g)(x) = f(g(x))$. The statement does not assert compactness; that is (2.14b).
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 495, in the proof of Theorem (3.2): "Clearly, supp [f,g] is contained in supp f union supp g. Moreover, since f, g are in PLF'(R), it follows from (2.14b) and (2.14c) that the closure of supp [f,g] is a compact subset of supp f union supp g." This statement is the containment half of that sentence; the compactness half is (2.14b), p. 493.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem closure_supp_commutator_subset {f g : ℝ ≃o ℝ}
    (hf : IsPLF f) (hg : IsPLF g) :
    closure (supp (f * g * f⁻¹ * g⁻¹)) ⊆ supp f ∪ supp g := by
  sorry

end BrinSquier
