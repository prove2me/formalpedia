-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_6_5
-- name    : DQILocal.Recon.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:29:48.522413+00:00
-- url     : https://prove2.me/theorems/5e5f61f0-e548-4533-9655-45fad077e06f
-- title:
--   Theorem 6.5, p. 40 — product amplitude functions with local decoders: $\beta\le\beta_d$ and expected cost per constraint $\ge\langle f\rangle_{p_{\beta_d}}-2(\max f-\min f)\sqrt{\varepsilon_n}$
-- statement:
--   Let $q\ge2$, $k,D\ge2$, let $f$ be a cost that is not constant, and let $\beta\ge0$. Let $(B_n)$ be a sequence of $(k,D)$-regular matrices with $m_n$ rows. For each $n$, let a coherent decoder for the decoding problem of $B_n$ with the product amplitude function $\Phi_\beta$ have block success at least $1-\varepsilon_n$, and suppose there are $t_n$ and $i_n$ such that $\mathrm{LT}_{t_n}(i_n)$ and $\mathrm{TP}_{t_n}(i_n)$ hold and the decoder makes a $t_n$-local estimate at $i_n$. If $\varepsilon_n\to0$, then:
--
--   1. $\beta\le\beta_d$;
--   2. for every $n$ with $\varepsilon_n<1$, the violation pattern $x$ output by DQI satisfies
--   $$\mathbb E_{x_0}\mathbb E\Bigl[\frac1{m_n}\sum_{j=1}^{m_n}f(x_j)\Bigr]\ge\langle f\rangle_{p_{\beta_d}}-2(\max f-\min f)\sqrt{\varepsilon_n};$$
--   3. for $q=2$ and $f(z)=z$, the expected satisfied fraction $\mathbb E_{x_0}\mathbb E[1-|x|/m_n]$ is at most $s_d+2\sqrt{\varepsilon_n}$ for every $n$ with $\varepsilon_n<1$, where $s_d=p_{\beta_d}(0)=\tfrac12+\tfrac12\tanh(\beta_d/2)$.
--
--   If $\beta_d=\infty$, then $p_{\beta_d}$ means $p_\infty$ (and $s_d=1$). So with a product amplitude function and a local decoder, DQI cannot reach an expected cost below its value at the reconstruction threshold.
--
--   **Formalization Note** The decoding problem uses the states $|\psi^{\Phi_\beta}_c\rangle$, which are the base product states (proved in the sanity file).
--
--   Differences from the source:
--   - encoding: "a decoder", run coherently by Regev's reduction → a coherent decoder (finite work type, initial work state, outcome map, unitary); its block success and local estimate are those of the POVM it induces; reason: Regev's reduction applies the decoder as a unitary dilation (proof of Theorem 3.3, p. 17); every POVM is induced by some coherent decoder
--   - encoding: "the violation pattern x output by DQI" and E_{x0} E[·] → regevLaw (the procedure of p. 17 as explicit linear maps) averaged over the q^m offsets by regevExpect; reason: Regev's reduction is the form of DQI the paper's statements refer to (p. 17)
--   - encoding: β ≤ β_d → ENNReal.ofReal β ≤ betaD k D q f; reason: β_d takes values in [0, ∞]
--   - encoding: max f − min f → (⨆ z, f z) − ⨅ z, f z over the finite set Z_q; reason: the supremum of a finite family is its maximum
--   - encoding: "for q = 2 and f(z) = z" → hypotheses q = 2 and ∀ z, f z = z.val inside the statement for general q; s_d read as 1 when β_d = ∞; reason: the clause applies exactly in that case; p_∞(0) = 1 for f(z) = z
--   - encoding: checks indexed by [n] → checks indexed by any finite type; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.5, p. 40

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Reconstruction
import Definitions.Def_DQILocal_Recon_Supplement_Amplitude
import Definitions.Def_DQILocal_Recon_Supplement_Regev
import Definitions.Def_DQILocal_Recon_Supplement_Thresholds

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon Filter Topology

/-- **Theorem 6.5 (Approximate optimization with product amplitude functions).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.5, p. 40.
"Let `q ≥ 2`, let `f` be a cost that is not constant, and let `β ≥ 0`. Let `(B_n)` be a sequence of
`(k, D)`-regular matrices with `m_n` rows. For each `n`, let a decoder for the decoding problem of
`B_n` with the product amplitude function `Φ_β` have block success at least `1 - ε_n`. Suppose that
for each `n` there are `t_n` and `i_n` such that `LT_{t_n}(i_n)` and `TP_{t_n}(i_n)` hold and the
decoder makes a `t_n`-local estimate at `i_n`. If `ε_n → 0`, then `β ≤ β_d`, and the violation
pattern `x` output by DQI satisfies, for every `n` with `ε_n < 1`,
`E_{x₀} E[(1/m_n) Σ_j f(x_j)] ≥ ⟨f⟩_{p_{β_d}} - 2(max f - min f)√ε_n`.
For `q = 2` and `f(z) = z`, the expected satisfied fraction is at most `s_d + 2√ε_n`, where
`s_d = p_{β_d}(0) = 1/2 + (1/2) tanh(β_d/2)`. If `β_d = ∞`, then `p_{β_d}` means `p_∞`."

**Formalization Note.** Each decoder is a coherent decoder (it is run by Regev's reduction, which
produces "the violation pattern output by DQI", law `regevLaw` averaged over `x₀` by
`regevExpect`); its block success and local estimate are those of its induced POVM for the states
`|ψ^{Φ_β}_c⟩` (`psiGen (phiProd p_β)`, equal to the base product states). `β_d = betaD ∈ [0, ∞]`,
so `β ≤ β_d` is `ENNReal.ofReal β ≤ β_d`; `p_{β_d}` is `pBetaD` (`p_∞` at `β_d = ∞`). `max f` and
`min f` are `⨆`/`⨅` over the finite set `ℤ_q`. The satisfied fraction of `x` for `f(z) = z` is
`1 - |x|/m_n`. `m_n ≥ 1` because the symbol `i_n ∈ [m_n]` exists. Standing assumptions `k ≥ 2`,
`D ≥ 2` (§3.1, p. 15). -/
theorem theorem_6_5 (k D q : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : 2 ≤ k) (hD : 2 ≤ D)
    (f : ZMod q → ℝ) (hf : ∃ z z' : ZMod q, f z ≠ f z') (β : ℝ) (hβ : 0 ≤ β)
    (m : ℕ → ℕ) (κ : ℕ → Type) [∀ n, Fintype (κ n)] (B : ∀ n, Matrix (Fin (m n)) (κ n) Bool)
    (hB : ∀ n, IsRegular k D (B n))
    (W : ℕ → Type) [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (Dec : ∀ n, CoherentDecoder q (m n) (W n)) (ε : ℕ → ℝ)
    (hsucc : ∀ n, 1 - ε n ≤ blockSuccessGen (phiProd (gibbsWeight q f β)) (B n) (inducedPOVM (Dec n)))
    (t : ℕ → ℕ) (i : ∀ n, Fin (m n))
    (hLT : ∀ n, LT (B n) (i n) (t n)) (hTP : ∀ n, TP q (B n) (i n) (t n))
    (hloc : ∀ n, IsLocalEstimateGen q (phiProd (gibbsWeight q f β)) (B n) (i n) (t n)
      (inducedPOVM (Dec n)))
    (hε : Tendsto ε atTop (𝓝 0)) :
    ENNReal.ofReal β ≤ betaD k D q f ∧
    (∀ n, ε n < 1 →
      avgCost (pBetaD k D q f) f - 2 * ((⨆ z, f z) - ⨅ z, f z) * Real.sqrt (ε n) ≤
        regevExpect (phiProd (gibbsWeight q f β)) (B n) (Dec n)
          (fun x => (1 / (m n : ℝ)) * ∑ j, f (x j))) ∧
    (q = 2 → (∀ z : ZMod q, f z = (z.val : ℝ)) → ∀ n, ε n < 1 →
      regevExpect (phiProd (gibbsWeight q f β)) (B n) (Dec n)
          (fun x => 1 - (hamWt x : ℝ) / (m n : ℝ)) ≤
        sdOf (betaD k D q f) + 2 * Real.sqrt (ε n)) := by sorry

end DQILocal.Recon.Supplement
