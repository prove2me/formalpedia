-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_5
-- name    : EffRobustLearn.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:36:11.302921+00:00
-- url     : https://prove2.me/theorems/ecb581e8-bfee-4765-a365-5771bcfd0139
-- title:
--   Lemma 3.5 — $K$ is convex, compact, of diameter $\le2\sqrt{|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|}$
-- statement:
--   For a class $C$ and samples $\bar S_{\mathrm{inp}},S_{\mathrm{ref}}$, the set $K=\mathrm{conv}\{c[S]:c\in C\}$ is convex and compact, with diameter
--   $$D_2\le2\sqrt{|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|}.$$
--
--   These are the geometric hypotheses of the online Frank–Wolfe theorem.
--
--   **Formalization Note** Compactness makes the metric diameter genuine, not the junk value of an unbounded set.
--
--   Differences from the source:
--   - generalization: nonempty samples and class, implicitly → also empty samples or an empty class; reason: the empty cases are trivial and the nonempty case is the source's
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.5, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_feasibleSet

namespace EffRobustLearn

/-- Lemma 3.5 (Feasible-set geometry), p.15 (arXiv:2609.17655, held version, sha256 312a0857…): `K = conv{c[S] : c ∈ C}` is convex and compact, with diameter at most
`2 √(|S̄inp| + |Sref|)`.

**Formalization Note.** `K` is compact, so `Metric.diam K` is the genuine diameter, not the junk value of an unbounded set. -/
theorem lemma_3_5 {X : Type*} {n m : ℕ} (C : Set (X → Bool)) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) :
    Convex ℝ (feasibleSet C Sinp Sref) ∧ IsCompact (feasibleSet C Sinp Sref) ∧
      Metric.diam (feasibleSet C Sinp Sref) ≤ 2 * Real.sqrt ((n : ℝ) + m) := by sorry

end EffRobustLearn
