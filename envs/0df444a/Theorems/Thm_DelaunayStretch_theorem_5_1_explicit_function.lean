-- Prove2me | Theorems.Thm_DelaunayStretch_theorem_5_1_explicit_function
-- name    : DelaunayStretch.theorem_5_1_explicit_function
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:58:29.152733+00:00
-- url     : https://prove2.me/theorems/8995e380-c3c4-416c-9470-e8d49cf0f0dc
-- title:
--   Theorem 5.1 — a function of the family $\mathcal H$ satisfies (H0)–(H4) at level $U_0=1.59485994$
-- statement:
--   Let $U_0=1.59485994$. There exists a function $H_\star$ in the family $\mathcal H$ of Definition 5.2 that satisfies conditions (H0)–(H4) at level $U_0$:
--
--   $$
--   \exists\,H_\star\in\mathcal H:\quad H_\star\ \text{satisfies (H0)–(H4) at level } U_0 .
--   $$
--
--   Membership in $\mathcal H$ means rational coefficients obeying the symmetries (5.3) and (5.4). Together with Theorem 4.7, this gives the chain inequality at level $U_0$; it is the computer-assisted step of the proof.
--
--   **Formalization Note** $U_0=159485994/10^8$ exactly. The conditions are in the sense of Definition 4.6, with respect to some piecewise $C^1$ structure. The paper's $H_\star$ has 3,150 coefficients stored in an external data file; they are not part of the statement.
--
--   Differences from the source:
--   - reading: the conditions are verified with respect to the piecewise C¹ structure of Definition 5.5 → (H0)–(H4) in the sense of Definition 4.6: with respect to some piecewise C¹ structure; reason: the headline claim is 'satisfies conditions (H0)–(H4)', whose definition quantifies the structure existentially; the sentence on Definition 5.5 names the witness used in the proof
--   - encoding: a, b defined by the linear system (5.1) → a, b given by the closed form (5.5); reason: Lemma 5.3: (5.5) is the unique solution of (5.1) on Ω, the only place H is read
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem 5.1, p.30

import Mathlib
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4
import Definitions.Def_DelaunayStretch_InFamilyH

namespace DelaunayStretch

/-- **Theorem 5.1 (The explicit function `H⋆`)** (p.30). Let `U₀ = 1.59485994`. There exists a
function `H⋆` in the parametrized family `𝓗` of Definition 5.2 that satisfies conditions
(H0)–(H4) at level `U₀`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem 5.1, p.30.

**Formalization Note** `U₀ = 159485994/10⁸` exactly. Membership in `𝓗` (rational coefficients
satisfying (5.3) and (5.4), `InFamilyH`) is part of the claim. "(H0)–(H4) at level `U₀`" is in
the sense of Definition 4.6: with respect to some piecewise `C¹` structure. The paper's witness
is the structure of Definition 5.5; the theorem's existential form does not fix it. The
3,150 coefficients of the paper's `H⋆` (data file of Appendix C.1) are not part of the
statement. -/
theorem theorem_5_1_explicit_function :
    ∃ H : R4 → ℝ, InFamilyH H ∧ SatisfiesH0toH4 (159485994 / 100000000 : ℝ) H := by sorry

end DelaunayStretch
