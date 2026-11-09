-- Prove2me | Theorems.Thm_CSPSubsample_lemma_3_2
-- name    : CSPSubsample.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:26:32.021658+00:00
-- url     : https://prove2.me/theorems/18d3a666-c528-4c4a-9a4e-b599a57dcac1
-- title:
--   Lemma 3.2 (Structure Lemma) (corrected: $|\Psi|\le q^{k^2s/\varepsilon}$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. For every $\varepsilon>0$, $N\in[n]$ and $1\le s<N$, and every $k$-CSP instance with $k\ge1$ and $q\ge1$, there is a nonempty set of assignments $\Psi\subseteq[q]^n$ with $|\Psi|\le q^{k^2s/\varepsilon}$ such that, for a uniformly random subset $U$ of size $N$,
--   $$
--   \mathbb E[\mathrm{OPT}(U)]\le\mathbb E\Big[\max_{\phi\in\Psi}\mathrm{val}_U(\phi)\Big]+\mathcal E(\varepsilon,N,s),
--   $$
--   $$
--   \mathcal E(\varepsilon,N,s)=C\Big(k\varepsilon+\frac{k^3}{s}+qN\exp\!\Big(-\frac{\varepsilon^2s}{2k^2}\Big)+\frac{k^2s^2}{\varepsilon N}+\frac{sk^3}{\varepsilon N}+\sqrt{\frac{k^4}{\varepsilon N}}+\frac{k^2}{\varepsilon}\exp\!\Big(-\frac{\varepsilon^2N}{k^4}\Big)\Big).
--   $$
--   $\Psi$ is chosen before $U$ and is the same for every $U$. Its size is small enough that a union bound of the concentration lemma over $\Psi$ costs only a factor $q^{k^2s/\varepsilon}$; this is the second of the two lemmas the subsampling theorem combines.
--
--   Differences from the source:
--   - correction: |Ψ| = q^{k²s/ε} → |Ψ| ≤ q^{k²s/ε} (real power); reason: the printed equality is false: n = 3, k = 1, q = 2, ε = 1/2, N = 3, s = 2 satisfy every assumption, and q^{k²s/ε} = 2⁴ = 16 > 8 = |[q]^n|, so no Ψ ⊆ [q]^n has that size; the proof gives |Ψ(S*)| ≤ q^{sT} with T = k²/ε, and Theorem 3.3 uses |Ψ| only as an upper bound
--   - reading: E(ε, N, s) = O(…) → C·(…) with one absolute constant C > 0 chosen before n, k, q, ε, N, s and the instance; reason: the paper's O-constants are absolute (none depends on a parameter); this is the uniform reading
--   - encoding: s < N, k, q unrestricted, Ψ ⊆ [q]^n → additionally 1 ≤ s, 1 ≤ k, 1 ≤ q and Ψ nonempty; reason: k³/s and exp(−ε²s/(2k²)) are undefined at s = 0 or k = 0, [q]^n is empty at q = 0 (n ≥ 1), and max over Ψ is undefined for Ψ = ∅
--   - encoding: E over a uniform random subset U of size N → the average over all N-subsets of [n]; reason: same law
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 3.2, p.6 (PDF p.8); proof §5, pp.11–23 (PDF pp.13–25)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valOn
import Definitions.Def_CSPSubsample_avgSub

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 3.2 (Structure Lemma)** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.6 = PDF p.8),
corrected: `|Ψ| ≤ q^{k²s/ε}` in place of the printed `|Ψ| = q^{k²s/ε}`. For every `ε > 0`,
`N ∈ [n]` and `s < N` there is a set of assignments `Ψ ⊆ [q]^n` such that, for a uniform random
subset `U` of size `N`, `E[OPT(U)] ≤ E[max_{ϕ ∈ Ψ} val_U(ϕ)] + E(ε, N, s)`, where
`E(ε,N,s) = O(kε + k³/s + qN exp(−ε²s/(2k²)) + k²s²/(εN) + sk³/(εN) + √(k⁴/(εN))
+ (k²/ε) exp(−ε²N/k⁴))`.

**Formalization Note** The `O(·)` constant `C` is absolute: it is chosen before every parameter.
`Ψ` is chosen after `n, k, q, ε, N, s` and the instance, and before `U`. `q^{k²s/ε}` is a real
power. `Ψ` is nonempty, so `max_{ϕ ∈ Ψ}` is defined. Correction of the printed `|Ψ| =`: for
`n = 3, k = 1, q = 2, ε = 1/2, N = 3, s = 2`, `q^{k²s/ε} = 16 > 8 = |[q]^n|`. `1 ≤ s`, `1 ≤ k`,
`1 ≤ q` exclude inputs where `k³/s`, `ε²s/(2k²)` or `[q]^n` is undefined or empty. -/
theorem lemma_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k q : ℕ) (ε : ℝ) (N s : ℕ), 0 < ε → 1 ≤ N → N ≤ n → s < N →
      1 ≤ s → 1 ≤ k → 1 ≤ q → ∀ I : Instance n k q,
      ∃ Ψ : Finset (Fin n → Fin q), Ψ.Nonempty ∧
        (Ψ.card : ℝ) ≤ (q : ℝ) ^ ((k : ℝ) ^ 2 * s / ε) ∧
        avgSub n N (OPTOn I) ≤ avgSub n N (fun U => maxOver Ψ (valOn I U)) +
          C * ((k : ℝ) * ε + (k : ℝ) ^ 3 / s +
            q * N * Real.exp (-(ε ^ 2 * s / (2 * (k : ℝ) ^ 2))) +
            (k : ℝ) ^ 2 * (s : ℝ) ^ 2 / (ε * N) + s * (k : ℝ) ^ 3 / (ε * N) +
            Real.sqrt ((k : ℝ) ^ 4 / (ε * N)) +
            (k : ℝ) ^ 2 / ε * Real.exp (-(ε ^ 2 * N / (k : ℝ) ^ 4))) := by sorry

end CSPSubsample
