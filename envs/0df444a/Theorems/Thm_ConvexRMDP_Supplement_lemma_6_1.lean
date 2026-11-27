-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_lemma_6_1
-- name    : ConvexRMDP.Supplement.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:00:45.271819+00:00
-- url     : https://prove2.me/theorems/99280ac3-7028-4c65-b106-6a2f0d7bc8fb
-- title:
--   Lemma 6.1 (corrected: $\xi_s\in\mathbb R^m_+$; Slater point feasible) — conjugate-dual maximization for $\tilde t(x)_s$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP with nonempty $\mathcal A$, satisfying Assumption 6.1 (with the corrected Slater condition) for convex constraint functions $g_{s,1}, \dots, g_{s,m} : \mathbb R^{\mathcal S \times \mathcal A} \to \mathbb R$, let $b > 0$ and $\omega_b(s,a) = \exp(b\,r_{sa})/|\mathcal A|$. For each $x \in [1,+\infty)^{\mathcal S}$ and $s \in \mathcal S$,
--
--   $$
--   \tilde t(x)_s = \max\; -\big(\xi_s^\top g_s\big)^*(y_s) + \sum_{a \in \mathcal A} \omega_b(s,a)\left( \min_{s' \in \mathcal S}\Big\{\alpha_{sa}\log(x_{s'}) + \frac{y_{sas'}}{\omega_b(s,a)}\Big\} - \frac{\alpha_{sa}}{\gamma}\log\Big(\frac{\alpha_{sa}}{\gamma}\Big) + \frac{\alpha_{sa}}{\gamma}\right)
--   $$
--
--   over $\xi_s \in \mathbb R^m_+$, $y_{sa} \in \mathbb R^{\mathcal S}$ and $\alpha_{sa} \in \mathbb R_+$ ($a \in \mathcal A$), and the maximum is attained. Here $(\xi_s^\top g_s)(P) = \sum_i \xi_{si} g_{s,i}(P)$ and $\tilde t$ is the operator (6.2).
--
--   Combined with Lemma 5.1 this gives the conic program (6.4) of Theorem 6.2.
--
--   **Formalization Note** The conjugate is taken on $\mathbb R^{\mathcal A \times \mathcal S}$ and may equal $+\infty$, so the objective is an extended real number; "max = value" is stated as: the value is attained at a feasible point and bounds every feasible objective value. $0 \log 0 = 0$.
--
--   Differences from the source:
--   - correction: $\xi_s \in \mathbb R^m$ → $\xi_s \in \mathbb R^m_+$; reason: with negative multipliers the equality fails: for $m = 1$ and the affine $g_{s,1} \equiv -1$ (so $\mathcal U_s = \Delta(\mathcal S)^{\mathcal A}$), $y_s = 0$ and $\xi_{s1} \to -\infty$ the objective tends to $+\infty$; the proof (App. F, p.33) and Theorem 6.2 use $\xi_s \in \mathbb R^m_+$.
--   - correction: Slater's condition of Assumption 6.1 → `Assumption61` (the Slater point also satisfies the affine constraints); reason: the attained maximum rests on strong duality with dual attainment (Boyd–Vandenberghe §5.2.3), whose refined Slater condition includes the affine constraints at the point.
--   - reading: "$\mathcal U_{sa} = \{p \in \Delta(\mathcal S)^{\mathcal A} \mid g_s(p) \le 0, \forall i\}$" in Assumption 6.1 → $\mathcal U_s = \{P \in \Delta(\mathcal S)^{\mathcal A} \mid g_{s,i}(P) \le 0\ \forall i\}$; reason: the model is s-rectangular (p.20).
--   - encoding: "proper closed convex $g_{s,i} : \mathbb R^{\mathcal S \times \mathcal A} \to \mathbb R$" → `ConvexOn ℝ univ`; reason: finite convex functions on a finite-dimensional space are proper and continuous.
--   - encoding: max of the printed program → `IsGreatest` of an `EReal`-valued objective; reason: Lean convention, attainment stated.
--   - encoding: nonempty $\mathcal A$ and $b>0$ → `[Nonempty A]` and `0 < b`; reason: standing assumptions required by the uniform weights and their denominators; no source instance is excluded.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Lemma 6.1, p.21; Assumption 6.1, p.20; proof in App. F, pp.33–34

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_Assumption61
import Definitions.Def_ConvexRMDP_Supplement_SRMDP_tOp
import Definitions.Def_ConvexRMDP_Supplement_conj

namespace ConvexRMDP

namespace Supplement

/-- **Lemma 6.1 (corrected: ξ_s ∈ ℝ^m_+; Slater point feasible)** (Grand-Clément & Petrik,
arXiv:2209.10187v2, p.21; proof in App. F, pp.33–34). Under Assumption 6.1, for each `x ∈ [1,+∞)^S`
and `s ∈ S`,
`t̃(x)_s = max −(ξ_sᵀ g_s)*(y_s) + ∑_a ω_b(s,a) (min_{s'}{α_{sa} log(x_{s'}) + y_{sas'}/ω_b(s,a)}
   − (α_{sa}/γ) log(α_{sa}/γ) + α_{sa}/γ)`
over `ξ_s ∈ ℝ^m_+`, `y_{sa} ∈ ℝ^S`, `α_{sa} ∈ ℝ₊` (`a ∈ A`), the maximum being attained.

**Formalization Note.** The page prints `ξ_s ∈ ℝ^m`; with a negative `ξ_{si}` and an affine `g_{s,i}`
with nonzero constant term the maximum is `+∞`, and the proof (App. F, p.33) and Theorem 6.2 use
`ξ_s ∈ ℝ^m_+`, which is stated here. Assumption 6.1 is `Assumption61` (corrected Slater). `t̃` is
`SRMDP.tOp` (6.2), `ω_b` is `SRMDP.omega`. `(ξ_sᵀ g_s)(P) = ∑_i ξ_{si} g_{s,i}(P)` and its conjugate is
taken on `ℝ^{A×S}` (uncurried `A × S → ℝ`). The objective is `EReal`-valued (the conjugate may be
`+∞`); "max … = value" is `IsGreatest`. Variables `q = (ξ_s, y_s, α_s)` with `y_s : A → S → ℝ`.
`min_{s'}` is the infimum over the finite set `S`, and `0 log 0 = 0`. `A` is nonempty and
`b > 0`, as required by the uniform weights. -/
theorem lemma_6_1 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : SRMDP S A) (b : ℝ) (hb : 0 < b) (m : ℕ) (g : S → Fin m → (A → S → ℝ) → ℝ)
    (hg : Assumption61 M m g) (x : S → ℝ) (hx : ∀ s', 1 ≤ x s') (s : S) :
    IsGreatest
      ((fun q : (Fin m → ℝ) × (A → S → ℝ) × (A → ℝ) =>
          -conj (fun P : A × S → ℝ => ((∑ i, q.1 i * g s i (Function.curry P) : ℝ) : EReal))
              (Function.uncurry q.2.1) +
            ((∑ a, M.omega b s a *
                ((⨅ s', (q.2.2 a * Real.log (x s') + q.2.1 a s' / M.omega b s a)) -
                  q.2.2 a / M.γ * Real.log (q.2.2 a / M.γ) + q.2.2 a / M.γ) : ℝ) : EReal)) ''
        {q | (∀ i, 0 ≤ q.1 i) ∧ ∀ a, 0 ≤ q.2.2 a})
      ((M.tOp b x s : ℝ) : EReal) := by sorry

end Supplement

end ConvexRMDP
