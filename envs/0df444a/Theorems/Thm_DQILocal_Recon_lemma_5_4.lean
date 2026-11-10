-- Prove2me | Theorems.Thm_DQILocal_Recon_lemma_5_4
-- name    : DQILocal.Recon.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:04.448118+00:00
-- url     : https://prove2.me/theorems/27a95df9-1420-4d9b-80d9-6e6ad3e15a46
-- title:
--   Lemma 5.4 — counting zero-sum labellings: $(s+1)^{q^{k-1}}\exp(s[\sum_jH(\pi_j)-\max_jH(\pi_j)])$ and $(s+1)^{q^{k-1}}\exp(s(k-1)H(\pi))$
-- statement:
--   Let $q\ge2$, $k\ge2$, $s\ge1$, $H(\pi)=-\sum_\gamma\pi(\gamma)\ln\pi(\gamma)$, and $\mathcal A_{q,k}=\{b\in\mathbb Z_q^k:\sum_jb_j=0\}$.
--
--   1. For each $j\in[k]$ let $\pi_j$ be a probability vector on $\mathbb Z_q$ with $s\pi_j(\gamma)\in\mathbb Z$. The number of sequences $(b(1),\dots,b(s))\in\mathcal A_{q,k}^s$ in which, for every $j$ and $\gamma$, exactly $s\pi_j(\gamma)$ entries have $j$-th coordinate $\gamma$ is at most
--   $$(s+1)^{q^{k-1}}\exp\Bigl(s\Bigl[\sum_jH(\pi_j)-\max_jH(\pi_j)\Bigr]\Bigr).$$
--   It is zero unless $\pi_j(\gamma)\le\sum_{i\ne j}(1-\pi_i(0))$ for every $j$ and every $\gamma\ne0$.
--   2. Let $\pi$ be a probability vector on $\mathbb Z_q$ with $ks\pi(\gamma)\in\mathbb Z$. The number of sequences in $\mathcal A_{q,k}^s$ in which, for every $\gamma$, exactly $ks\pi(\gamma)$ of the $ks$ coordinates equal $\gamma$ is at most
--   $$(s+1)^{q^{k-1}}\exp\bigl(s(k-1)H(\pi)\bigr).$$
--   It is zero if $\pi(\gamma)>1-1/k$ for some $\gamma$ with $k\gamma\ne0$.
--
--   The zero-sum constraint at each symbol reduces the entropy by at least that of one coordinate; this is the counting step of the first-moment bound for vectors of linear support.
--
--   Differences from the source:
--   - encoding: H(π) = −Σ π(γ) ln π(γ) → Σ_γ Real.negMulLog (π γ); reason: negMulLog x = −x ln x with 0 ln 0 = 0
--   - encoding: max_j H(π_j) → ⨆ j : Fin k, H(π_j); reason: Fin k is finite and nonempty (k ≥ 2), so the supremum is the maximum
--   - encoding: "it is zero unless π_j(γ) ≤ Σ_{i≠j}(1 − π_i(0)) for every j and every γ ≠ 0" → if some j and γ ≠ 0 have Σ_{i≠j}(1 − π_i(0)) < π_j(γ), the count is 0; reason: the same implication
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.4, p. 32

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra

namespace DQILocal.Recon

open scoped BigOperators

/-- **Lemma 5.4 (Counting zero-sum labellings).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.4, p. 32, with
`H(π) = -Σ_γ π(γ) ln π(γ)` and `A_{q,k} = {b ∈ ℤ_q^k : Σ_j b_j = 0}` (p. 32).
"Let `q ≥ 2`, `k ≥ 2`, and `s ≥ 1`.
1. For each `j ∈ [k]` let `π_j` be a probability vector on `ℤ_q` with `sπ_j(γ) ∈ ℤ`. The number of
   sequences `(b(1), …, b(s)) ∈ A^s_{q,k}` in which, for every `j` and `γ`, exactly `sπ_j(γ)`
   entries have `j`-th coordinate `γ` is at most
   `(s + 1)^{q^{k-1}} exp(s[Σ_j H(π_j) - max_j H(π_j)])`. It is zero unless
   `π_j(γ) ≤ Σ_{i≠j}(1 - π_i(0))` for every `j` and every `γ ≠ 0`.
2. Let `π` be a probability vector on `ℤ_q` with `ksπ(γ) ∈ ℤ`. The number of sequences in
   `A^s_{q,k}` in which, for every `γ`, exactly `ksπ(γ)` of the `ks` coordinates equal `γ` is at most
   `(s + 1)^{q^{k-1}} exp(s(k - 1)H(π))`. It is zero if `π(γ) > 1 - 1/k` for some `γ` with
   `kγ ≠ 0`."

**Formalization Note.** `H` uses `Real.negMulLog` (`0 ln 0 = 0`). A sequence is
`b : Fin s → Fin k → ℤ_q`; `max_j` is `⨆ j` over the nonempty finite `Fin k`. -/
theorem lemma_5_4 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (hs : 1 ≤ s) :
    let H : (ZMod q → ℝ) → ℝ := fun π => ∑ γ : ZMod q, Real.negMulLog (π γ)
    let A : Finset (Fin s → Fin k → ZMod q) :=
      Finset.univ.filter fun b => ∀ r : Fin s, ∑ j : Fin k, b r j = 0
    (∀ π : Fin k → ZMod q → ℝ, (∀ j, IsProbVec (π j)) →
      (∀ j γ, ∃ n : ℤ, (s : ℝ) * π j γ = n) →
        ((A.filter fun b => ∀ j γ,
            ((Finset.univ.filter fun r : Fin s => b r j = γ).card : ℝ) = s * π j γ).card : ℝ) ≤
          ((s : ℝ) + 1) ^ (q ^ (k - 1)) *
            Real.exp (s * (∑ j : Fin k, H (π j) - ⨆ j : Fin k, H (π j))) ∧
        ((∃ j : Fin k, ∃ γ : ZMod q, γ ≠ 0 ∧
            ∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≠ j), (1 - π i 0) < π j γ) →
          (A.filter fun b => ∀ j γ,
            ((Finset.univ.filter fun r : Fin s => b r j = γ).card : ℝ) = s * π j γ).card = 0)) ∧
    (∀ π : ZMod q → ℝ, IsProbVec π → (∀ γ, ∃ n : ℤ, (k : ℝ) * s * π γ = n) →
        ((A.filter fun b => ∀ γ,
            ((Finset.univ.filter fun rj : Fin s × Fin k => b rj.1 rj.2 = γ).card : ℝ) =
              k * s * π γ).card : ℝ) ≤
          ((s : ℝ) + 1) ^ (q ^ (k - 1)) * Real.exp (s * ((k : ℝ) - 1) * H π) ∧
        ((∃ γ : ZMod q, (k : ZMod q) * γ ≠ 0 ∧ 1 - 1 / (k : ℝ) < π γ) →
          (A.filter fun b => ∀ γ,
            ((Finset.univ.filter fun rj : Fin s × Fin k => b rj.1 rj.2 = γ).card : ℝ) =
              k * s * π γ).card = 0)) := by sorry

end DQILocal.Recon
