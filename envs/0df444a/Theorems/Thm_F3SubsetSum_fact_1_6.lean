-- Prove2me | Theorems.Thm_F3SubsetSum_fact_1_6
-- name    : F3SubsetSum.fact_1_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:28:54.578205+00:00
-- url     : https://prove2.me/theorems/ff805c90-4a91-4b79-9403-ff6b6293406c
-- title:
--   Fact 1.6 — uniqueness thresholds for Binary-Error LWE, pointwise in $(s,e)$
-- statement:
--   Let $q\ge3$ be prime, $\kappa_q=\log_{q/2}q$, and $\eta>0$. There is $c>0$ (depending on $q,\eta$) such that for all $n,m$, all $s\in\mathbb F_q^n$ and $e\in\{0,1\}^m$, with $A$ uniform in $\mathbb F_q^{n\times m}$ and $\mathcal C$ the candidate set of $(A,A^\top s+e)$:
--
--   1. if $m\ge(\kappa_q+\eta)n$, then $\Pr_A[\mathcal C=\{s\}]\ge 1-2^{-cm}$;
--   2. if $m\le(\kappa_q-\eta)n$, then $\Pr_A[\mathcal C=\{s\}]\le 2^{-cn}$.
--
--   So $m\approx\kappa_qn$ samples are needed for the secret to be determined at all, and the threshold $\kappa>\log_{q/2}q$ of Theorem 1.7 is information-theoretically necessary.
--
--   Differences from the source:
--   - reading: a unique solution s exists → the planted s is the only candidate: 𝒞(A, A⊤s + e) = {s}, for every fixed s and e; reason: App. B fixes s and e and calls s the unique secret exactly when no other candidate exists (p.42)
--   - reading: 2^{−Ω_{q,η}(m)}, 2^{−Ω_{q,η}(n)} → ∃ c > 0 depending only on q and η with the bounds for every n, m, s, e in the range, one c for both clauses; reason: the strongest reading of Ω; the proof's bounds hold for all n, m
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Fact 1.6, p.5 (proof App. B, pp.42–43)

import Mathlib
import Definitions.Def_F3SubsetSum_BinaryErrorLWE
import Definitions.Def_F3SubsetSum_QuotientAlgebra

namespace F3SubsetSum

open Classical in
/-- **Fact 1.6** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Fact 1.6, p.5;
proof App. B, pp.42–43): "Let κ_q = log_{q/2}(q) and let η > 0 be any constant. For
Problem 1.5, if m ≥ (κ_q + η) · n, a unique solution s exists with probability at least
1 − 2^{−Ω_{q,η}(m)}; if m ≤ (κ_q − η) · n, a unique solution s exists with probability at most
2^{−Ω_{q,η}(n)}."

For a fixed prime `q ≥ 3` (Problem 1.5, p.5), fixed `s ∈ F_qⁿ` and `e ∈ {0,1}^m` (App. B, p.42:
"Fix s ∈ F_q^n and e ∈ {0, 1}^m"), the probability is over `A` uniform in `F_q^{n×m}` that the
planted secret is the unique candidate, `𝒞(A, A⊤s + e) = {s}` (eq. (26)).

**Formalization Note** `2^{−Ω_{q,η}(·)}` is read as: there is `c > 0`, depending on `q` and `η`
only, such that the bound holds for every `n`, `m`, `s`, `e` in the stated range; one `c` serves
both clauses. -/
theorem fact_1_6 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ) (s : Fin n → ZMod q) (e : Fin m → Bool),
      ((Real.logb ((q : ℝ) / 2) q + η) * n ≤ m →
        1 - (2 : ℝ) ^ (-(c * m)) ≤
          ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
            candidates A (lweSample A s e) = {s}).card : ℝ) / (q : ℝ) ^ (n * m)) ∧
      ((m : ℝ) ≤ (Real.logb ((q : ℝ) / 2) q - η) * n →
        ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
            candidates A (lweSample A s e) = {s}).card : ℝ) / (q : ℝ) ^ (n * m) ≤
          (2 : ℝ) ^ (-(c * n))) := by sorry

end F3SubsetSum
