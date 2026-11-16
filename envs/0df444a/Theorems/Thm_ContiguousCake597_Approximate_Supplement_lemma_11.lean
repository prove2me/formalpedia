-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_Supplement_lemma_11
-- name    : ContiguousCake597.Approximate.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:44.455266+00:00
-- url     : https://prove2.me/theorems/4798d994-ee01-41a6-b68c-06db3aca2e9f
-- title:
--   Lemma 11 — PPAD-hardness of contiguous EFc and EFc-outer for binary exclusive equal-count goods
-- statement:
--   Fix any integer $c\ge0$ (including $c=0$). Consider goods on a path with binary valuations in which every good has value $1$ for exactly one agent and value $0$ for all others, and all agents value the same number of goods. Then the search problem of computing a contiguous EF$c$ allocation on such instances is PPAD-hard: every search problem in PPAD reduces to it by a polynomial-time search reduction. The same holds with EF$c_{\mathrm{outer}}$ in place of EF$c$:
--   $$\forall R\in\mathrm{PPAD}:\quad R\le_p \textsc{EF}c\text{-Path}_{\mathrm{bin}},\qquad R\le_p \textsc{EF}c_{\mathrm{outer}}\text{-Path}_{\mathrm{bin}}.$$
--   Only hardness is asserted; totality of the relation is not claimed by this statement. This lemma supplies the hardness half of Theorem 2 for a fixed budget.
--
--   Differences from the source:
--   - encoding: "computing ... is PPAD-hard" → every problem of the published class PPAD search-reduces to the encoded relation whose answers are all complete contiguous allocations satisfying the notion; reason: the standard meaning of PPAD-hardness of a search problem with the paper's encodings
--   - reading: n agents → n ≥ 1 agents; reason: the paper's standing convention (with no agents and at least one good there is no allocation); it only restricts the target instances, which the reduction must produce
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 11 (PDF 12), Lemma 11; proof p. 12 (PDF 13)

import Definitions.Def_ContiguousCake597_Approximate_Supplement_Path

namespace ContiguousCake597.Approximate.Supplement

/-- Lemma 11, printed p.11 (PDF 12), proof printed p.12 (PDF 13). For every fixed
`c ≥ 0`, contiguous goods EFc and EFc_outer search are PPAD-hard on binary
exclusive-ownership equal-count instances. Hardness only; no totality is asserted. -/
theorem lemma_11 (c : ℕ) :
    (∀ R ∈ QuasiStrictNE.PPAD,
      CardinalMatching.SearchReduces R (PathProblem false false (.const c) true)) ∧
    (∀ R ∈ QuasiStrictNE.PPAD,
      CardinalMatching.SearchReduces R (PathProblem false true (.const c) true)) := by sorry

end ContiguousCake597.Approximate.Supplement
