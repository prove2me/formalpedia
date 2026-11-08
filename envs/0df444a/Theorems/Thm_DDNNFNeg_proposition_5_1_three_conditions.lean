-- Prove2me | Theorems.Thm_DDNNFNeg_proposition_5_1_three_conditions
-- name    : DDNNFNeg.proposition_5_1_three_conditions
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:22:38.258033+00:00
-- url     : https://prove2.me/theorems/91bc108a-ebc8-4ee2-8fc8-b07f9876a76e
-- title:
--   Proof of Proposition 5.1 — $f_G(x)=1$ iff one of three mutually exclusive colour conditions holds
-- statement:
--   Let $G$ be a graph on $[n]$ with an edge colouring by the colours $1, 2, 3$, and for $x \in \{0,1\}^{[n]}$ write $H_c$ for "$G_x$ contains colour $c$". Then
--   $$
--   f_G(x) = 1 \iff (H_1 \wedge \neg H_2) \vee (H_2 \wedge \neg H_3) \vee (H_3 \wedge \neg H_1),
--   $$
--   and the three conditions $H_1 \wedge \neg H_2$, $H_2 \wedge \neg H_3$, $H_3 \wedge \neg H_1$ are pairwise mutually exclusive.
--
--   This rewrites $f_G$ as a disjunction of three disjoint events, each computable by a small OBDD, which is how the linear d-DNNF upper bound is obtained.
--
--   **Formalization Note** Colours $1, 2, 3$ are $0, 1, 2 \in \mathrm{Fin}\,3$.
--
--   Differences from the source:
--   - generalization: G 3-regular with a proper 3-edge-colouring → any graph on Fin n and any colouring by three colours; reason: the equivalence and the exclusivity are propositional and use neither regularity nor properness; the paper's G is a special case
--   - encoding: colours 1, 2, 3 → 0, 1, 2 : Fin 3; reason: Lean convention; same instances
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), proof of Proposition 5.1, p.11

import Mathlib
import Definitions.Def_DDNNFNeg_fG

namespace DDNNFNeg

/-- **Proof of Proposition 5.1**, the three exclusive conditions (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.11): `f_G(x) = 1` if
and only if `G_x` contains colour 1 but not colour 2, or colour 2 but not colour 3, or colour 3
but not colour 1; and the three conditions are mutually exclusive.

**Formalization Note** Colours `1, 2, 3` are `0, 1, 2 : Fin 3`. The statement holds for every
graph on `Fin n` and every colouring, so the paper's 3-regularity and properness are not
assumed. -/
theorem proposition_5_1_three_conditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Sym2 (Fin n) → Fin 3) (x : Fin n → Bool) :
    (fG G c x = true ↔
      (HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∨ (HasColor G c x 1 ∧ ¬ HasColor G c x 2) ∨
        (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) ∧
    ¬ ((HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∧ (HasColor G c x 1 ∧ ¬ HasColor G c x 2)) ∧
    ¬ ((HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∧ (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) ∧
    ¬ ((HasColor G c x 1 ∧ ¬ HasColor G c x 2) ∧ (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) := by sorry

end DDNNFNeg
