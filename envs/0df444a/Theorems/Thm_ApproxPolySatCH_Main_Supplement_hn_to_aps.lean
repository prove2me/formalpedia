-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_Supplement_hn_to_aps
-- name    : ApproxPolySatCH.Main.Supplement.hn_to_aps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:55:01.458588+00:00
-- url     : https://prove2.me/theorems/89d16de0-52f3-4ead-b211-5af9ddd71559
-- title:
--   Theorem 15 — Hilbert Nullstellensatz reduces to APS
-- statement:
--   Fix $k=\mathbb Q$ or any finite field, presented as $\mathbb F_p[U]/(\mu)$ with $p$ prime and $\mu$ monic irreducible of positive degree. The Hilbert Nullstellensatz problem asks whether the input tuple has an exact common zero over $\overline{k}$; APS asks whether the origin lies in its Zariski image closure. Using the same sparse polynomial input encoding with binary exponents,
--   $$\mathrm{HN}_{k,\mathrm{sparse}}\leq_m^{\mathrm P}\mathrm{APS}_{k,\mathrm{sparse}}.$$
--   For each fixed coefficient field there exist a single deterministic finite program, constants $c,d\in\mathbb N$ and a total output function $r$ such that on every word $w$ the program computes $r(w)$ within $c(|w|+1)^d$ steps, and
--   $$w\in\mathrm{HN}_{k,\mathrm{sparse}}\iff r(w)\in\mathrm{APS}_{k,\mathrm{sparse}}.$$
--   All finite characteristics are included. There is no bound on polynomial degree, coefficient height, variable count or equation count. Empty, all-zero, constant and malformed inputs are handled by the actual decision languages.
--
--   This result relates exact feasibility to approximate feasibility in both coefficient regimes. No effective Nullstellensatz certificate or correctness promise is supplied as a hypothesis.
--
--   Differences from the source:
--   - encoding: HN_k and APS_k with the default sparse bit encoding over Q or a finite field → HNSparseLanguage k and published SparseLanguage k for every CoefficientField k, under published ManyOneReduction; reason: uses the same input systems and validity, algebraic-closure semantics, and a finite deterministic program with a polynomial clock on all binary words
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Theorem 15, p.26–27 (PDF p.26–27), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=26

import Definitions.Def_ApproxPolySatCH_Main_Supplement_HilbertNullstellensatz

set_option autoImplicit false

namespace ApproxPolySatCH.Main.Supplement

/-- Theorem 15, pp.26–27: both coefficient regimes, with the source's sparse encoding. -/
theorem hn_to_aps (k : CoefficientField) :
    ManyOneReduction (HNSparseLanguage k) (SparseLanguage k) := by sorry

end ApproxPolySatCH.Main.Supplement
