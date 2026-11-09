-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_6
-- name    : DirTeleMC.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:44.19231+00:00
-- url     : https://prove2.me/theorems/c5a772d1-66d8-4771-9472-db366bcdae08
-- title:
--   Lemma B.6 — the top call returns a structure with loads at most $\Gamma(\ln\nu + (1+\ln k)/4)$
-- statement:
--   Let $\ell \ge 2$, $\eta = 2\ell - 1$, $\theta \ge 1$, $\Lambda > 0$, $\Gamma \ge 4e(e-1)\eta\Lambda$, $s \notin K$, and let the demand $k$ satisfy $1 \le k \le |K|$.
--
--   **Lemma B.6 (top call).** Suppose that a structure $J'$ rooted at the root of $\mathcal U_{\eta,\theta}$ covers at least $k$ terminals, has maximum load at most $\Lambda$, and has positive loads on at most $\nu$ vertices. Then GREEDY(root of $\mathcal U_{\eta,\theta}$, $k$, $0$, $K$) has a run, and for every run the returned structures together form a structure $J$ that covers at least $k$ terminals, with every load at most
--   $$\Gamma\left(\ln \nu + \frac{1 + \ln k}{4}\right).$$
--
--   Differences from the source:
--   - encoding: the demand k at most |K| → 1 ≤ k ≤ |K|; reason: Algorithm 1 takes a demand z ≥ 1
--   - encoding: the structures returned by GREEDY → a run exists, and the claim holds for every run; reason: the page leaves the minimizing choices open; every choice is covered
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.6, p.30 (PDF p.31); proof pp.30–31 (PDF pp.31–32)

import Mathlib
import Definitions.Def_DirTeleMC_GreedyLoop

namespace DirTeleMC

/-- **Lemma B.6** (the top call).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.6, p.30: "Let θ ≥ 1 and Λ > 0, let Γ ≥ 4e(e − 1)ηΛ, and let the demand k be at most the number of
terminals in K. Suppose that a structure J′ rooted at the root of U_{η,θ} covers at least k terminals, has
maximum load at most Λ, and has positive loads on a set V′ of at most ν vertices of G. Then the structures
returned by GREEDY(root of U_{η,θ}, k, 0, K) together form a structure J that covers at least k terminals, and
every load of J is at most Γ(ln ν + (1 + ln k)/4)."

For `ℓ ≥ 2`, `η = 2ℓ − 1`, `θ ≥ 1`, `Λ > 0`, `Γ ≥ 4e(e − 1)ηΛ`, a source `s ∉ K` and a demand `1 ≤ k ≤ |K|`: if a
structure `J′` rooted at the root of `U_{η,θ}` covers at least `k` terminals, has maximum load at most `Λ` and
positive loads on at most `ν` vertices, then the top call `GREEDY(root, k, 0, K)` has a run, and for every run
the union `J` of the returned structures is a structure rooted at the root of `U_{η,θ}` that covers at least `k`
terminals, with every load at most `Γ(ln ν + (1 + ln k)/4)`.

**Formalization Note.** `1 ≤ k` is Algorithm 1's input condition "z ≥ 1"; `s ∉ K` is the standing
`K ⊆ V \ {s}`, used in the proof ("The source s is in V′"). `Real.log` is the natural logarithm. -/
theorem lemma_B_6 {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) (K : Finset (Fin n)) (hsK : s ∉ K)
    (θ ℓ : ℕ) (hθ : 1 ≤ θ) (hℓ : 2 ≤ ℓ) (Λ Γ : ℝ) (hΛ : 0 < Λ)
    (hΓΛ : 4 * Real.exp 1 * (Real.exp 1 - 1) * ((2 * ℓ - 1 : ℕ) : ℝ) * Λ ≤ Γ)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K.card) (J' : JTree n)
    (hJ' : JTree.IsStructure adj θ (2 * ℓ - 1) J') (hJ's : J'.label = s)
    (hcov : k ≤ (K ∩ JTree.cov (2 * ℓ - 1) J').card) (hΛJ' : (J'.maxLoad : ℝ) ≤ Λ) (ν : ℕ)
    (hν : (Finset.univ.filter fun v => 0 < J'.loads v).card ≤ ν) :
    (∃ out, GreedyRun adj θ Γ s (2 * ℓ - 1) k 0 K out) ∧
    ∀ out, GreedyRun adj θ Γ s (2 * ℓ - 1) k 0 K out →
      JTree.IsStructure adj θ (2 * ℓ - 1) (JTree.join s out) ∧
        k ≤ (K ∩ JTree.cov (2 * ℓ - 1) (JTree.join s out)).card ∧
        ∀ v, ((JTree.join s out).loads v : ℝ) ≤ Γ * (Real.log ν + (1 + Real.log k) / 4) := by sorry

end DirTeleMC
