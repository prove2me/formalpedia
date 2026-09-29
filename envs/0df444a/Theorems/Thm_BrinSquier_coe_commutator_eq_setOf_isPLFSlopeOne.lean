-- Prove2me | Theorems.Thm_BrinSquier_coe_commutator_eq_setOf_isPLFSlopeOne
-- name    : BrinSquier.coe_commutator_eq_setOf_isPLFSlopeOne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T20:23:33.593986+00:00
-- url     : https://prove2.me/theorems/370376d5-da97-4886-a56f-a17716fabaa6
-- title:
--   p. 493 — the commutator subgroup of PLF(ℝ) is exactly the maps of slope one at each end
-- statement:
--   Let $\mathrm{PLF}(\mathbb{R})$ be the group of piecewise-linear homeomorphisms of the real line with finitely many breakpoints. Brin and Squier identify its commutator subgroup:
--
--   $$\mathrm{PLF}'(\mathbb{R}) \;=\; \{\, f \in \mathrm{PLF}(\mathbb{R}) : f \text{ has slope } 1 \text{ near } -\infty \text{ and near } +\infty \,\}.$$
--
--   Having slope $1$ near an end means agreeing with a single map $t \mapsto t + c$ on a ray out to that end; the two constants are unconstrained and independent, so this is **not** a compact-support condition — every translation satisfies it.
--
--   **Role.** One inclusion is the statement that a commutator has slope $1$ at each end, which is the source's (2.14a) together with the fact that the slope-one maps form a subgroup. The reverse inclusion is the substantial half, and it is what licenses reading a hypothesis of slope one at both ends as membership in $\mathrm{PLF}'(\mathbb{R})$ — which is how Brin and Squier state the results that rest on it, including their Theorem (3.2). Brin and Squier assert the identification without proof, saying the reverse inclusion follows from an argument like the one that shows their generators (2.1) generate $\mathrm{PLF}(\mathbb{R})$: their normal-form theorem (2.3) writes every $f$ uniquely as $M_p T_a X_{b_1,q_1} \cdots X_{b_n,q_n}$, where $M_p(t) = pt$, $T_a(t) = t + a$, and $X_{b,q}$ is the identity to the left of $b$ with slope $q$ to its right.
--
--   **Formalization note.** $\mathrm{PLF}(\mathbb{R})$ enters as a subgroup $G$ of the order isomorphisms of $\mathbb{R}$ pinned by the hypothesis that its members are exactly the piecewise-linear maps with finitely many breakpoints, rather than as a new definition. Such a subgroup exists — closure under composition and inverse are separate results — so the hypothesis is satisfiable and the statement is not vacuous. The conclusion is an equality of carrier sets, matching the source's "consists precisely of", and the predicate on the right already includes piecewise linearity, so it also asserts membership in $\mathrm{PLF}(\mathbb{R})$.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 493: "It is easy to see that the commutator subgroup PLF'(R) of PLF(R) consists precisely of those elements of PLF(R) which have slope 1 near -oo and +oo. One inclusion follows directly from (2.14a) and the other follows from an argument similar to the proof that the homeomorphisms defined in (2.1) generate PLF(R)." PROVENANCE: the source asserts this without proof and delegates the reverse inclusion to an argument analogous to its normal-form theorem (2.3); it is not a numbered result there.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem coe_commutator_eq_setOf_isPLFSlopeOne
    (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ IsPLF f) :
    (↑⁅G, G⁆ : Set (ℝ ≃o ℝ)) = {f | IsPLFSlopeOne f} := by
  sorry

end BrinSquier
