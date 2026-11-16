-- Prove2me | Theorems.Thm_CoDecompFO_Supplement_theorem_5_53
-- name    : CoDecompFO.Supplement.theorem_5_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:52:37.013207+00:00
-- url     : https://prove2.me/theorems/978a3b9b-33b1-4caf-bd68-333acf5b7a6c
-- title:
--   Theorem 5.53 — the total categories $\mathrm{Strat}^\sigma_m$ and $\mathrm{HTh}^\sigma_m$ have pullbacks, preserved by the projections
-- statement:
--   Fix $0\le m\le\ell$ and suppose that the category of positions $\mathrm{Pos}^\sigma_m$ has pullbacks. Then the total category of $m$-strategies $\mathrm{Strat}^\sigma_m$ and the total category of $m$-hypotheticals $\mathrm{HTh}^\sigma_m$ have pullbacks, and the projection functors
--
--   $$p:\mathrm{Strat}^\sigma_m\to\mathrm{Pos}^\sigma_m,\qquad p:\mathrm{HTh}^\sigma_m\to\mathrm{Pos}^\sigma_m$$
--
--   preserve them.
--
--   This is what allows the full-FO dynamic program to combine local strategies and hypotheticals along the pullbacks that build the limit of a co-decomposition, as hypotheses are combined in the $\exists$-FO case.
--
--   **Formalization Note** The total categories are the unreduced diagrammatic ones of ¶5.33 and ¶5.35 (empty families allowed), with positions over $\sigma$-structures in `Type` and assignments of length $2(\ell-m)$; a morphism $(f,\eta)$ carries $\eta:f_*A\to B$ written out over $f$.
--
--   Differences from the source:
--   - encoding: the Grothendieck construction of (G,β) ↦ X_m(G,β) with morphisms (f, η : f_*A → B) → StratTot / HThTot: morphisms (f, η) with η a morphism over f (StratHom / HThHom); reason: a morphism f_*A → B out of the fibre concatenations is exactly this data, so the hom-sets and composition agree; the coherence isomorphisms are built in
--   - encoding: σ-structures G, hypotheses N → G with N = [k] → carriers in Type; a hypothesis as a set of atoms on [k] with β a homomorphism from its head; reason: a hypothesis with a fixed underlying assignment is determined by its head
--   - encoding: the projection functors preserve pullbacks → PreservesLimitsOfShape WalkingCospan; reason: Mathlib’s notion of preserving pullbacks
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 5.53, p.28 (PDF p.30); ¶5.24–5.50, pp.22–28; proof pp.28–33 (PDF pp.30–35)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_HThTotal

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory Limits

/-- **Theorem 5.53** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, p.28; proof pp.29–33): "Fix 0 ≤ m ≤ ℓ and suppose that the category
of positions Pos^σ_m has pullbacks. Then the total categories Strat^σ_m and HTh^σ_m have pullbacks, and their
projection functors to Pos^σ_m preserve them."

**Formalization Note** `Pos^σ_m` is `Pos σ (2(ℓ−m))`, positions over σ-structures with carriers in `Type`. The
total categories are the Grothendieck constructions of ¶5.50, presented by morphisms over maps of positions
(`StratTot.category`, `HThTot.category`): a morphism `(f, η)` carries `η : f_* A → B` written out through the
universal property of the concatenations in `f_*`. They are the unreduced diagrammatic categories of ¶5.33 and
¶5.35, with empty families allowed (¶5.25). The hypothesis on `Pos^σ_m` is kept as printed. -/
theorem theorem_5_53 (σ : Sig) (ℓ m : ℕ) (hm : m ≤ ℓ) [HasPullbacks (Pos σ (2 * (ℓ - m)))] :
    (HasPullbacks (StratTot σ m (2 * (ℓ - m))) ∧
      PreservesLimitsOfShape WalkingCospan (StratTot.proj σ m (2 * (ℓ - m)))) ∧
    (HasPullbacks (HThTot σ m (2 * (ℓ - m))) ∧
      PreservesLimitsOfShape WalkingCospan (HThTot.proj σ m (2 * (ℓ - m)))) := by sorry

end Supplement

end CoDecompFO
