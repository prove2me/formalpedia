-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_6_9
-- name    : DQILocal.Recon.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:30:50.028493+00:00
-- url     : https://prove2.me/theorems/c9964c6f-033d-486f-80ca-d189e41b3533
-- title:
--   Theorem 6.9, p. 42 — symmetric amplitude functions, two-level cost, local decoders: $\kappa_\eta>0$, bound (15), and satisfied fraction $\le p_{\beta_d}(A)+o(1)$
-- statement:
--   Let $q\ge2$, $k,D\ge2$, and let $f(z)=c+\Delta\,\mathbf 1[z\notin A]$ with $\Delta>0$ and $A$ a nonempty proper subset of $\mathbb Z_q$; assume that its reconstruction threshold $\beta_d$ is finite. Write $H_A(x)$ for the number of $j$ with $x_j\notin A$. Let $(B_n)$ be a sequence of $(k,D)$-regular matrices with $m_n$ rows; for each $n$ let $\Phi_n$ be a symmetric amplitude function and let a coherent decoder for the decoding problem of $B_n$ with amplitude function $\Phi_n$ have block success at least $1-\varepsilon_n$. Suppose that for each $n$ there are $t_n,i_n$ with $\mathrm{LT}_{t_n}(i_n)$, $\mathrm{TP}_{t_n}(i_n)$, and the decoder makes a $t_n$-local estimate at $i_n$; write $v_n=|N_{t_n}(i_n)|$. For $\eta>0$ let $s_\eta=p_{\beta_d+\eta}(A)$ and $\kappa_\eta=1-P_\infty(p_{\beta_d+\eta})$. Then:
--
--   1. $\kappa_\eta>0$ for every $\eta>0$ (and $\kappa_\eta$ depends only on $(k,D,q,f,\eta)$);
--   2. for every $\eta>0$ and every $n$ with $\varepsilon_n<1$, the violation pattern $x$ output by DQI satisfies
--   $$\mathbb E_{x_0}\mathbb E\Bigl[1-\frac{H_A(x)}{m_n}\Bigr]\le s_\eta+\frac{\varepsilon_n+4v_n/m_n}{\kappa_\eta}+\frac{4v_n}{m_n}+2\sqrt{\varepsilon_n};\tag{15}$$
--   3. if $\varepsilon_n\to0$ and $v_n/m_n\to0$, the expected satisfied fraction is at most $p_{\beta_d}(A)+o(1)$ and the expected cost per constraint is at least $\langle f\rangle_{p_{\beta_d}}-o(1)$;
--   4. for Max-XORSAT ($q=2$, $A=\{0\}$, $c=0$, $\Delta=1$), under the same limits, the expected satisfied fraction is at most $s_d+o(1)$, $s_d=\tfrac12+\tfrac12\tanh(\beta_d/2)$.
--
--   So no symmetric amplitude function lets DQI with a local decoder beat the satisfied fraction at the reconstruction threshold.
--
--   **Formalization Note** The local estimate and block success are those of the states $Z^c|\Phi_n\rangle$, not of product states.
--
--   Differences from the source:
--   - encoding: "a decoder", run coherently by Regev's reduction → a coherent decoder (finite work type, initial work state, outcome map, unitary); its block success and local estimate are those of the POVM it induces; reason: Regev's reduction applies the decoder as a unitary dilation (proof of Theorem 3.3, p. 17); every POVM is induced by some coherent decoder
--   - encoding: "the violation pattern x output by DQI" and E_{x0} E[·] → regevLaw (the procedure of p. 17 as explicit linear maps) averaged over the q^m offsets by regevExpect; reason: Regev's reduction is the form of DQI the paper's statements refer to (p. 17)
--   - encoding: "≤ a + o(1)" and "≥ a − o(1)" → for every δ > 0, eventually ≤ a + δ (resp. ≥ a − δ); reason: the definition of o(1) along n → ∞
--   - encoding: P_∞ = lim_t P_t → Pinf, the supremum over t of P_t; reason: P_t is nondecreasing and bounded; same value
--   - encoding: Max-XORSAT → hypotheses q = 2, A = {0}, c = 0, Δ = 1, satisfied fraction 1 − |x|/m_n; reason: f(z) = z is the two-level cost with these parameters (§6.2.2, p. 41)
--   - encoding: checks indexed by [n] → checks indexed by any finite type; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.9, p. 42; §6.2.2, p. 41

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Reconstruction
import Definitions.Def_DQILocal_Recon_Supplement_Amplitude
import Definitions.Def_DQILocal_Recon_Supplement_Regev
import Definitions.Def_DQILocal_Recon_Supplement_Thresholds

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon Filter Topology

/-- **Theorem 6.9 (Approximate optimization with symmetric amplitude functions).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.9, p. 42.
"Let `q ≥ 2`, let `f(z) = c + Δ 1[z ∉ A]` with `Δ > 0` be a cost that takes two values, and assume
that its reconstruction threshold `β_d` is finite. Let `(B_n)` be a sequence of `(k, D)`-regular
matrices with `m_n` rows. For each `n`, let `Φ_n` be a symmetric amplitude function, and let a
decoder for the decoding problem of `B_n` with amplitude function `Φ_n` have block success at least
`1 - ε_n`. Suppose that for each `n` there are `t_n` and `i_n` such that `LT_{t_n}(i_n)` and
`TP_{t_n}(i_n)` hold and the decoder makes a `t_n`-local estimate at `i_n`, and write
`v_n = |N_{t_n}(i_n)|`. For `η > 0`, let `s_η = p_{β_d+η}(A)` and `κ_η = 1 - P_∞(p_{β_d+η})`, where
`P_∞ = lim_t P_t`; then `κ_η > 0`, and it depends only on `(k, D, q, f, η)`. The violation pattern
`x` output by DQI satisfies, for every `n` with `ε_n < 1`,
`E_{x₀} E[1 - H_A(x)/m_n] ≤ s_η + (ε_n + 4v_n/m_n)/κ_η + 4v_n/m_n + 2√ε_n`. (15)
In particular, if `ε_n → 0` and `v_n/m_n → 0`, the expected satisfied fraction is at most
`p_{β_d}(A) + o(1)`, and the expected cost per constraint is at least `⟨f⟩_{p_{β_d}} - o(1)`. For
Max-XORSAT, the expected satisfied fraction is at most `s_d + o(1)`."

**Formalization Note.**
* `A` is a nonempty proper subset of `ℤ_q` (§6.2.2, p. 41); `H_A(x) = #{j : x_j ∉ A}` (`violA`).
* Each decoder is a coherent decoder; its block success and local estimate are those of its induced
  POVM for the states `Z^c|Φ_n⟩ = psiGen Φ_n c` (p. 41: "Definition 3.4 applies to them"), not of
  product states. The output law is `regevLaw`, averaged over the offset by `regevExpect`.
* `s_η` and `κ_η` are the functions `sEta`, `kappaEta` of `(k, D, q, f, A, η)`, so "depends only on
  `(k, D, q, f, η)`" holds by construction. `β_d` is finite by hypothesis and enters as `β_d.toReal`.
* "`≤ a + o(1)`" is: for every `δ > 0`, eventually `≤ a + δ`; similarly for "`≥ a - o(1)`".
* Max-XORSAT is `q = 2`, `A = {0}`, `c = 0`, `Δ = 1` (so `f(z) = z`), with satisfied fraction
  `1 - |x|/m_n` and `s_d = ½ + ½ tanh(β_d/2)` (`sdOf`).
* `m_n ≥ 1` because `i_n ∈ [m_n]`. Standing assumptions `k ≥ 2`, `D ≥ 2` (§3.1, p. 15). -/
theorem theorem_6_9 (k D q : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : 2 ≤ k) (hD : 2 ≤ D)
    (A : Finset (ZMod q)) (hA : A.Nonempty) (hAu : A ≠ Finset.univ) (c Δ : ℝ) (hΔ : 0 < Δ)
    (f : ZMod q → ℝ) (hf : ∀ z, f z = c + Δ * (if z ∈ A then 0 else 1))
    (hβd : betaD k D q f ≠ ⊤)
    (m : ℕ → ℕ) (κ : ℕ → Type) [∀ n, Fintype (κ n)] (B : ∀ n, Matrix (Fin (m n)) (κ n) Bool)
    (hB : ∀ n, IsRegular k D (B n))
    (Φ : ∀ n, (Fin (m n) → ZMod q) → ℂ) (hΦ : ∀ n, IsAmplitude (Φ n))
    (hsym : ∀ n, IsSymmetricAmp f (Φ n))
    (W : ℕ → Type) [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (Dec : ∀ n, CoherentDecoder q (m n) (W n)) (ε : ℕ → ℝ)
    (hsucc : ∀ n, 1 - ε n ≤ blockSuccessGen (Φ n) (B n) (inducedPOVM (Dec n)))
    (t : ℕ → ℕ) (i : ∀ n, Fin (m n))
    (hLT : ∀ n, LT (B n) (i n) (t n)) (hTP : ∀ n, TP q (B n) (i n) (t n))
    (hloc : ∀ n, IsLocalEstimateGen q (Φ n) (B n) (i n) (t n) (inducedPOVM (Dec n))) :
    let v : ℕ → ℝ := fun n => ((ballSym (B n) (i n) (t n)).card : ℝ)
    let sat : ℕ → ℝ := fun n =>
      regevExpect (Φ n) (B n) (Dec n) (fun x => 1 - (violA A x : ℝ) / (m n : ℝ))
    (∀ η : ℝ, 0 < η → 0 < kappaEta k D q f η) ∧
    (∀ η : ℝ, 0 < η → ∀ n, ε n < 1 →
      sat n ≤ sEta k D q f A η + (ε n + 4 * v n / (m n : ℝ)) / kappaEta k D q f η +
        4 * v n / (m n : ℝ) + 2 * Real.sqrt (ε n)) ∧
    (Tendsto ε atTop (𝓝 0) → Tendsto (fun n => v n / (m n : ℝ)) atTop (𝓝 0) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        sat n ≤ ∑ z ∈ A, gibbsWeight q f (betaD k D q f).toReal z + δ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        avgCost (gibbsWeight q f (betaD k D q f).toReal) f - δ ≤
          regevExpect (Φ n) (B n) (Dec n) (fun x => (1 / (m n : ℝ)) * ∑ j, f (x j)))) ∧
    (q = 2 → A = {0} → c = 0 → Δ = 1 →
      Tendsto ε atTop (𝓝 0) → Tendsto (fun n => v n / (m n : ℝ)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        regevExpect (Φ n) (B n) (Dec n) (fun x => 1 - (hamWt x : ℝ) / (m n : ℝ)) ≤
          sdOf (betaD k D q f) + δ) := by sorry

end DQILocal.Recon.Supplement
