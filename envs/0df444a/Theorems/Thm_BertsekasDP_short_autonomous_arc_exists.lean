-- Prove2me | Theorems.Thm_BertsekasDP_short_autonomous_arc_exists
-- name    : BertsekasDP.short_autonomous_arc_exists
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T22:51:14.933155+00:00
-- url     : https://prove2.me/theorems/49e65578-1bab-4067-a7bb-8ec8f05541d2
-- title:
--   Short autonomous solution arcs with a linear displacement bound
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be continuously differentiable, let $q\in\mathbb R^n$ and $\tau\in\mathbb R$, and let $a_\varepsilon\in\mathbb R^n$ be a family of initial states. Suppose there is a real constant $C$ such that, for all sufficiently small positive $\varepsilon$,
--
--   $$\|a_\varepsilon-q\|\le C\varepsilon.$$
--
--   There exist a family of curves $y_\varepsilon:\mathbb R\to\mathbb R^n$ and a real constant $K$ such that, for all sufficiently small positive $\varepsilon$, the curve is continuous on $[\tau-\varepsilon,\tau]$ and satisfies
--
--   $$y_\varepsilon(\tau-\varepsilon)=a_\varepsilon,\qquad
--   \dot y_\varepsilon(t)=f(y_\varepsilon(t))\quad(\tau-\varepsilon<t<\tau),$$
--
--   $$\sup_{\tau-\varepsilon\le t\le\tau}\|y_\varepsilon(t)-q\|\le K\varepsilon.$$
--
--   This quantitative local-existence corollary supplies the constant-control portion of a needle perturbation. It imposes no global Lipschitz condition on $f$ and no continuity of the parameter map $\varepsilon\mapsto a_\varepsilon$. It specializes the local-existence and bounded-velocity estimates in the cited reference to shrinking time intervals.
--
--   **Formalization Note.** Curves are defined on all real times but constrained only on the stated interval. The dimension may be zero; the eventual conditions concern positive widths only.
-- source:
--   Dalibor Pražák, Carathéodory theory of ODEs (fall 2024), https://www.karlin.mff.cuni.cz/~prazak/vyuka/Odr2/Skripta/en_acODR-24.pdf, Theorem 6 and integral equation (3), p. 2; Lemma 16 and its integrated-velocity estimate, p. 7. Quantitative autonomous corollary for initial displacement O(ε), not a verbatim numbered theorem. Needle application: D. Liberzon, Calculus of Variations and Optimal Control Theory, §4.2.3, equations (4.12)-(4.14), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html.

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.short_autonomous_arc_exists
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ 1 f)
    (q : EuclideanSpace ℝ (Fin n)) (a : ℝ → EuclideanSpace ℝ (Fin n))
    (τ C : ℝ)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖a ε - q‖ ≤ C * ε) :
    ∃ (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ContinuousOn (y ε) (Set.Icc (τ - ε) τ) ∧
        y ε (τ - ε) = a ε ∧
        (∀ t ∈ Set.Ioo (τ - ε) τ, HasDerivAt (y ε) (f (y ε t)) t) ∧
        (∀ t ∈ Set.Icc (τ - ε) τ, ‖y ε t - q‖ ≤ K * ε) := by
  sorry
