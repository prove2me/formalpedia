-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_6_3
-- name    : ArbSlowFP.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:18.691548+00:00
-- url     : https://prove2.me/theorems/ced32c4f-2ab1-4858-926a-97493d6772d3
-- title:
--   Lemma 6.3 — endpoint-action identities (33), (34)
-- statement:
--   Fix an order-$k$ clock, a scale $\tau\ge1$, a gain $c\in(0,1)$, a margin $0<\delta<\min\{c,\delta_0\}$ and $H=A_k+3$. For $q$ with $\tau q\ge Q_k$, consider the old-block scores during the parent bundle $W_k(\tau q)\cdots W_k(2\tau q-1)$ starting from $s(q)=Sp_k(q)$, with remaining parent counts $z^{\mathrm{rem}}$. Then
--   $$u_g-u_b=\delta-vz^{\mathrm{rem}} .$$
--   Consequently $g$ loses to the parent maximum by at least $\delta_0-\delta>0$ at every proper prefix, and exceeds it by $\delta$ at the exact bundle endpoint. After the single play of $g$, the parent maximum is $u_b=\zeta(q)-c$ and $u_g=\zeta(q)-c+\delta$. Moreover
--   $$S_{b,:}=\zeta B,\quad (S_{\mathrm{mid}})_{b,:}=\zeta-ce_{0,w}^\top,\quad (S_{\mathrm{mid}})_{g,:}=\zeta-(c-\delta)e_{0,w}^\top,$$
--   $$S_{:,k}=(S_{\mathrm{mid}})_{:,k}=\zeta_k\mathbf 1_{m+1},\quad D_{:,k}=0,\quad \zeta_k=\chi_{k-1}\tau^{k-1}(2^{k-1}-1)>0,$$
--   and $D$ does not depend on $\delta$.
--
--   **Formalization Note** The scores are those of the old-block game $G_O$ under parent words. The parent maximum is the height restricted to the parent actions.
--
--   Differences from the source:
--   - encoding: the parameters τ, c, δ of the fixed construction, with H = A_k + 3 → stated for every τ ≥ 1, every c ∈ (0,1) and every 0 < δ < min{c, δ₀}; reason: these are the ranges stated at (27)–(28) on p.36
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.39, Lemma 6.3

import Mathlib
import Definitions.Def_ArbSlowFP_ValidFrom
import Definitions.Def_ArbSlowFP_IsAddData

open Matrix

namespace ArbSlowFP

/-- Lemma 6.3, p.39 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). The old-block score
tables (27)–(28) of an order-k clock at scale `τ ≥ 1`, gain `c ∈ (0,1)`, margin `0 < δ < min{c, δ₀}` and
`H = A_k + 3`. For each `q` with `τq ≥ Q_k`, along the bundle `W_k(τq) ⋯ W_k(2τq-1)` from `s(q)`:

(33) `u_g - u_b = δ - vz^rem`; `g` loses to the parent maximum by at least `δ₀ - δ > 0` at every proper
prefix and exceeds it by `δ` at the endpoint; after the single play of `g`, the parent maximum is
`u_b = ζ(q) - c` and `u_g = ζ(q) - c + δ`. Moreover (34): `S_{b,:} = ζB`, `(S_mid)_{b,:} = ζ - ce⊤₀`,
`(S_mid)_{g,:} = ζ - (c-δ)e⊤₀`, `S_{:,k} = (S_mid)_{:,k} = ζ_k 1`, `D_{:,k} = 0`, with
`ζ_k = χ_{k-1}τ^{k-1}(2^{k-1}-1) > 0`; and `D` does not depend on `δ`.

**Formalization Note.** The scores are those of the old-block game `G_O` only, under parent words; the
endpoint action is `Sum.inr ()`, the parent actions are `Sum.inl i`. The parent maximum is the height of
the restriction to parent actions. -/
theorem lemma_6_3 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (hτ : 1 ≤ τ) (c δ : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hδ0 : 0 < δ) (hδc : δ < c) (hδd : δ < d.δ0) :
    let P := d.parent
    let H := d.Ak + 3
    let ζ := P.zeta H τ c
    let s : ℕ → ι ⊕ Unit → ℚ := fun q => P.S H τ c δ *ᵥ binomBasis (k + 1) (q : ℤ)
    let word : ℕ → List (ι ⊕ Unit) := fun q => (bundle d.W (τ * q) (τ * q)).map Sum.inl
    let u : ℕ → ℕ → ι ⊕ Unit → ℚ := fun q n => scoreAfter P.GO (s q) ((word q).take n)
    let parentMax : (ι ⊕ Unit → ℚ) → ℚ := fun x => height fun i => x (Sum.inl i)
    (∀ q, d.Q ≤ τ * q → ∀ n, n ≤ (word q).length →
      u q n (Sum.inr ()) - u q n (Sum.inl d.b) =
        δ - d.v ⬝ᵥ wordCount ((bundle d.W (τ * q) (τ * q)).drop n)) ∧
    0 < d.δ0 - δ ∧
    (∀ q, d.Q ≤ τ * q → ∀ n, n < (word q).length →
      d.δ0 - δ ≤ parentMax (u q n) - u q n (Sum.inr ())) ∧
    (∀ q, d.Q ≤ τ * q →
      u q (word q).length (Sum.inr ()) - parentMax (u q (word q).length) = δ) ∧
    (∀ q, d.Q ≤ τ * q →
      let uEnd := scoreAfter P.GO (s q) (word q ++ [Sum.inr ()])
      parentMax uEnd = uEnd (Sum.inl d.b) ∧
      uEnd (Sum.inl d.b) = ζ ⬝ᵥ binomBasis (k + 1) (q : ℤ) - c ∧
      uEnd (Sum.inr ()) = ζ ⬝ᵥ binomBasis (k + 1) (q : ℤ) - c + δ) ∧
    P.S H τ c δ (Sum.inl d.b) = ζ ᵥ* shiftB (k + 1) ∧
    P.Smid H τ c δ (Sum.inl d.b) = ζ - c • e0Row (k + 1) ∧
    P.Smid H τ c δ (Sum.inr ()) = ζ - (c - δ) • e0Row (k + 1) ∧
    (∀ x, P.S H τ c δ x (Fin.last k) = ζ (Fin.last k)) ∧
    (∀ x, P.Smid H τ c δ x (Fin.last k) = ζ (Fin.last k)) ∧
    (∀ x, P.D H τ c δ x (Fin.last k) = 0) ∧
    ζ (Fin.last k) = lastCoef (d.R d.b) * (τ : ℚ) ^ (k - 1) * (2 ^ (k - 1) - 1) ∧
    0 < ζ (Fin.last k) ∧
    ∀ δ' : ℚ, P.D H τ c δ' = P.D H τ c δ := by sorry

end ArbSlowFP
