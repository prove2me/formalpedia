-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_pinning_conditioning
-- name    : ChenCapacityTerminals.Exact.pinning_conditioning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:27.601801+00:00
-- url     : https://prove2.me/theorems/b29127da-e803-45c2-82f9-5b060b8dcc97
-- title:
--   Corollary 4.1 — Exact pinning and conditioning
-- statement:
--   Under the numeric hypotheses of Theorem 2.1, use the original masses $b(r)=1$ and $b(v)=1+\deg^-(v)$ on other vertices, and write $M=m+n$. Construct the terminals with
--   $$t_d=\left\lceil\frac{Md}{n}\right\rceil.$$
--   Their number is $\widetilde O(n/d)$ and construction costs $\widetilde O(Md)$ for every guess. If $L\le\lambda$, identifying the terminals, the root and any additional vertices gives a conditioned graph on the surviving original masses, at rate
--   $$\eta_d=\frac{L}{4d(3+\lceil\log_2n\rceil)t_d}.$$
--   Every subset of the surviving nonroots, including the empty subset, has exactly its original entering capacity. The preservation assertion holds regardless of whether $L$ is a good lower bound.
--
--   This is the original-cut guarantee needed when selected terminals are pinned; it makes no claim about cuts containing pinned vertices.
--
--   Differences from the source:
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: L ≤ λ for the rooted minimum λ → every nonempty root-avoiding shore has entering capacity at least L; reason: this is the same lower-bound assertion without choosing an optimizer or taking a default-valued infimum
--   - encoding: identify any further vertices with the root → quantify over every surviving subset S and form the explicit restriction to S; reason: retaining S is equivalent to pinning its exterior; surviving masses stay attached to their original labels
--   - encoding: the legal SCC, cover and guide choices in Sections 2.1–2.3 → LegalConstruction records the full recipe including a postorder extension for arbitrary masses; reason: every legal guide has this extension; no size, expansion or time conclusion is assumed
--   - encoding: O and soft-O resource guarantees → positive constants and logarithm exponents quantified before the instances; actual finite-program executions and network traces; reason: uniform constants replace asymptotic notation without fixing an unsupported numeral or granting free graph operations
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 8, PDF p. 9, Corollary 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=9

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem pinning_conditioning :
    ∃ C : ℝ, ∃ k : ℕ, ∃ P : List TrulySubcubicAPSP.Instr, 0 < C ∧ PinningTime P ∧
      ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ),
        TerminalParameters G r d L (indegreeMass G.network r) (separatorThreshold G.network d) →
        (∃ c, LegalConstruction G.network r d L
          (indegreeMass G.network r) (separatorThreshold G.network d) c) ∧
        ∀ c, LegalConstruction G.network r d L
          (indegreeMass G.network r) (separatorThreshold G.network d) c →
            PinningShape C k G.network r d L c := by sorry

end ChenCapacityTerminals.Exact
