-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_lemma_4_muLim_hasDerivAt
-- name    : EquilibriumExperiment.Gradient.lemma_4_muLim_hasDerivAt
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T13:41:10.638353+00:00
-- url     : https://prove2.me/theorems/8266c9ed-7e23-405d-aa4e-b18624654412
-- title:
--   Lemma 4 (3.20), p. 19 — mean-field part: $\mu_a$ is differentiable at $p$ with derivative $\mu'_a(p)=\Delta_a(p)/(1+\dots)$
-- statement:
--   Consider a market satisfying the standing assumptions (Definition 5, Assumptions 1–3, (3.1)–(3.2)), conditional on a global state $A=a$. Fix $p>0$ with $\mathbb E[f_B(p\,\bar\omega)]>0$, and let $\mu_a(p)$ be the mean-field active supply, the unique solution in $(0,1]$ of $\mu=\mathbb E[f_{B_1}(p\,\omega(d_a/\mu))]$ (Lemma 2). Then $\mu_a$ is differentiable at $p$, with
--   $$\mu_a'(p)=\frac{\Delta_a(p)}{1+p\,d_a\,\Delta_a(p)\,\omega'\bigl(d_a/\mu_a(p)\bigr)\big/\bigl(\mu_a(p)^2\,\omega(d_a/\mu_a(p))\bigr)},\qquad \Delta_a(p)=\omega\bigl(d_a/\mu_a(p)\bigr)\,\mathbb E\bigl[f'_{B_1}\bigl(p\,\omega(d_a/\mu_a(p))\bigr)\bigr].$$
--   This is the mean-field statement in the second equality of (3.20). It says the right-hand side of (3.20) is the true derivative of $p\mapsto\mu_a(p)$, independently of the finite-$n$ limit in the first equality. It is the ingredient Proposition 12 needs.
--
--   **Formalization Note.** $\mu_a(p)$ is `muLim p` and the right-hand side is `muLimDeriv p`, with Lean's convention $x/0=0$. In the degenerate case $\omega(d_a/\mu_a(p))=0$, concavity forces $\omega\equiv0$ on $\mathbb R_+$, so $\mu_a$ is locally constant and both sides equal $0$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 19, Lemma 4, eq. (3.20) (second equality: μ'_a(p) = Δ_a(p)/(1 + p d_a Δ_a(p) ω'(d_a/μ_a(p))/(μ_a(p)² ω(d_a/μ_a(p)))))

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem lemma_4_muLim_hasDerivAt {B : Type} [MeasurableSpace B] (M : Market B)
    (hM : M.Standing) {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β) :
    HasDerivAt M.muLim (M.muLimDeriv p) p := by sorry

end EquilibriumExperiment.Gradient
