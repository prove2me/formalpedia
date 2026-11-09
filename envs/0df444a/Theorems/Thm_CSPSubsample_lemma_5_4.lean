-- Prove2me | Theorems.Thm_CSPSubsample_lemma_5_4
-- name    : CSPSubsample.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:55.573193+00:00
-- url     : https://prove2.me/theorems/caa78f3e-f2ea-41c3-979a-f75d09b15bc5
-- title:
--   Lemma 5.4 — under $\gamma$, $\mathrm{OPT}^{\mathrm{bal}}(U)-\max_{\Psi(\mathcal S)}\mathrm{val}^{\mathrm{bal}}_U\le 2k(\varepsilon+(k-1)^2/s)$ w.h.p.
-- statement:
--   Let $(U,\mathcal S)\sim\gamma$, where $U$ takes $N/T$ variables from each block and $S_t$ takes $s$ variables from $U\setminus U_t$. Then, with probability at least
--   $$
--   1-2qN\exp\!\Big(-\frac{\varepsilon^2s}{2(k-1)^2}\Big)-\frac{2Ts^2}{N},
--   $$
--   it holds that
--   $$
--   \mathrm{OPT}^{\mathrm{bal}}(U)-\max_{\phi\in\Psi(\mathcal S)}\mathrm{val}^{\mathrm{bal}}_U(\phi)\le 2k\Big(\varepsilon+\frac{(k-1)^2}{s}\Big).
--   $$
--   The family $\Psi(\mathcal S)$ depends only on the seed sets, not on $U$; this is what lets the structure lemma replace the optimum over all $q^n$ assignments by a maximum over a family of size $q^{sT}$.
--
--   Differences from the source:
--   - generalization: blocks V_1, …, V_T of size approximately n/T → an arbitrary block map b : [n] → [T]; reason: the statement holds for every partition of [n] into T blocks; it specializes to the paper's blocks
--   - generalization: ties in arg max broken in an arbitrary but deterministic way, consistently in (6) and (7) → an arbitrary maximizer-choosing rule tb (which may depend on the variable i), the same rule in (6) and (7); reason: the paper's rule is one such rule
--   - encoding: a seed σ̄ ∈ ⨉_{t∈[T]} [q]^{S_t} → σ : [T] → [n] → [q], of which only σ_t on S_t is read; reason: the extender reads σ_t only on S_t, so the two seed spaces give the same assignments
--   - encoding: (U, S) ∼ γ, sampled in two uniform stages → the uniform law on the valid pairs {(U, S) : |U ∩ V_t| = N/T, S_t ⊆ U ∖ U_t, |S_t| = s ∀t}; reason: both stages are uniform over families of constant size (|U ∖ U_t| = N − N/T), so every valid pair has the same probability
--   - encoding: γ with |U_t| = N/T drawn from V_t and |S_t| = s drawn from U ∖ U_t → T ∣ N, N/T ≤ |V_t| for every t, 1 ≤ s ≤ N − N/T; reason: the conditions under which γ is defined (s ≥ 1 also makes (k − 1)²/s defined)
--   - reading: exp(−ε²s/(2(k−1)²)) at k = 1 (zero denominator) → the value 0 at k = 1 (the limit as the denominator tends to 0⁺); reason: the printed expression is undefined at k = 1; the stronger reading holds, because for k = 1 the best response is exactly optimal and the gap is 0
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 5.4, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valOn
import Definitions.Def_CSPSubsample_valbal
import Definitions.Def_CSPSubsample_extender
import Definitions.Def_CSPSubsample_gamma

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 5.4** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.16 = PDF p.18). Let `(U, S) ∼ γ`.
Then with probability at least `1 − 2qN exp(−ε²s/(2(k−1)²)) − 2Ts²/N`,
`OPT^bal(U) − max_{ϕ ∈ Ψ(S)} val^bal_U(ϕ) ≤ 2k(ε + (k−1)²/s)`.

**Formalization Note** `γ` is the uniform law on the valid pairs (`probGamma`); `Ψ(S)` is built
from eq. (6) with an arbitrary tie-breaking rule `tb`; the block map `b` is arbitrary.
`T ∣ N`, `N/T ≤ |V_t|` and `1 ≤ s ≤ N − N/T` are the conditions under which `γ` is defined
(`N/T` variables are drawn from each block and `s` from `U ∖ U_t`). At `k = 1` the printed
`exp(−ε²s/(2(k−1)²))` has a zero denominator; it is read as its limit `0`. -/
theorem lemma_5_4 {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T) (N s : ℕ) (ε : ℝ)
    (tb : Fin n → (Fin q → ℝ) → Fin q) (htb : IsArgmaxRule tb) (hTN : T ∣ N)
    (hV : ∀ t, N / T ≤ (blockPart b Finset.univ t).card) (hs : 1 ≤ s) (hsN : s ≤ N - N / T)
    (hε : 0 < ε) :
    1 - 2 * q * N * (if k = 1 then 0 else Real.exp (-(ε ^ 2 * s / (2 * ((k : ℝ) - 1) ^ 2)))) -
        2 * T * (s : ℝ) ^ 2 / N ≤
      probGamma b N s (fun p => OPTbal I b p.1 - maxOver (Psi I b p.2 tb) (valbal I b p.1) ≤
        2 * k * (ε + ((k : ℝ) - 1) ^ 2 / s)) := by sorry

end CSPSubsample
