-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_Supplement_path_touch
-- name    : FlowOptimalSeparators.MinorFree.Supplement.path_touch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:00:49.875455+00:00
-- url     : https://prove2.me/theorems/e8cafc79-216c-426d-987b-ccd02e6ad989
-- title:
--   Proposition 1 — induced-minor-free path touch probability
-- statement:
--   There is an absolute constant $c_1>0$ with the following property. Let $H$ be a nonempty finite graph and $G$ an $H$-induced-minor-free graph. Let $\pi$ be any probability distribution on $V(G)$; sample $u,v$ independently from $\pi$, then sample a simple $u$–$v$ path $P$ from any fixed distribution for that ordered pair, taking $P=\{u\}$ when $u=v$. For an independent copy $P'$,
--   $$\Pr\bigl[P\text{ and }P'\text{ share a vertex or are joined by an edge}\bigr]\ \ge\ \frac{c_1}{|V(H)|+|E(H)|}.$$
--   This is the induced-minor counterpart of the shared-vertex collision bound for $K_h$-minor-free graphs; it drives the objective bound of Lemma 5 and hence the termination of Section 5's Cluster-FTRL.
--
--   Differences from the source:
--   - encoding: finite simple graphs H and G on arbitrary vertex sets → SimpleGraph (Fin a) and SimpleGraph (Fin n), with |V(H)| = a; reason: vertex relabelling preserves induced minors, paths, components and edge counts
--   - encoding: u, v sampled from π, then a simple u–v path from any fixed distribution for that ordered pair, P = {u} if u = v → an endpoint law π on Fin n and a nonnegative kernel κ supported on simple u–v paths, normalized for every ordered pair of positive-mass endpoints, equal to the one-vertex path on the diagonal; the probability is a finite double sum over vertex lists; reason: same instances; a positive-mass pair in different components has no u–v path, so the source process is undefined there as well
--   - encoding: c1 > 0 is an absolute constant → ∃ c1 > 0 quantified before H, G, π and κ; reason: an absolute constant depends on none of the data
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 5, 20–21, Proposition 1

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree.Supplement

/-- Proposition 1, p.5 (restated p.20): one absolute `c₁ > 0` for every nonempty `H`, every
`H`-induced-minor-free `G`, every endpoint law `π` and every normalized simple-path kernel `κ`
(diagonal path `[u]`). The event is "share a vertex or are joined by an edge". -/
theorem path_touch :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {a n : ℕ} (H : Graph a) (G : Graph n), 0 < a → InducedMinorFree H G →
        ∀ (π : Fin n → ℝ), EndpointLaw π →
        ∀ (κ : Fin n → Fin n → List (Fin n) → ℝ), PathKernel G π κ →
          c₁ / ((a : ℝ) + edgeCount H) ≤ touchProbability G π κ := by sorry

end FlowOptimalSeparators.MinorFree.Supplement
