-- Prove2me | Theorems.Thm_AFIsingKS_Supplement_theorem_B_5
-- name    : AFIsingKS.Supplement.theorem_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:24:29.330194+00:00
-- url     : https://prove2.me/theorems/285f7942-d352-47d5-a366-96a2a41a7b83
-- title:
--   Theorem B.5, p.73 — unconditioned truncated second moment, eq. (129)
-- statement:
--   Let $d\ge3$, consider the configuration model on $n$ clouds of $d$ sockets with $nd$ even and $N=nd$, and let $M$ be the uniformly random perfect matching. For $\varepsilon>0$ let $Z^{(2)}_{M,<\varepsilon}(\beta)=\sum e^{\beta H_M(\sigma^1)+\bar\beta H_M(\sigma^2)}$, summed over pairs of configurations with $|R(\sigma^1,\mathbf 1)|,|R(\sigma^2,\mathbf 1)|,|R(\sigma^1,\sigma^2)|<\varepsilon$. Put $p=e^\beta$, $q=e^{\bar\beta}$, $h(\beta)=(1+p)(1+q)$, $\delta_2(\beta)=\frac{p-1}{p+1}\frac{q-1}{q+1}$ and $K_\eta(\rho)=\{\beta\in\mathbb C:\operatorname{dist}(\beta,[0,(1-\eta)\beta_{\mathrm{KS}}])\le\rho\}$.
--
--   Fix $0<\eta<1$. There exist $\rho=\rho(d,\eta)>0$ and $\varepsilon_0=\varepsilon_0(d,\eta)>0$ such that, for every $\beta\in K_\eta(\rho)$ and every $0<\varepsilon\le\varepsilon_0$,
--   $$\mathbb E_M\big[Z^{(2)}_{M,<\varepsilon}(\beta)\big]=\Big(1+O\Big(\frac1n\Big)\Big)\,4^n\Big(\frac{h(\beta)}4\Big)^{N/2}\frac{\sqrt{h(\beta)}}{\sqrt{(d(p-1)+2)(d(q-1)+2)}}\cdot\frac1{\sqrt{1-(d-1)\delta_2(\beta)}},$$
--   with the $O(1/n)$ uniform in $\beta\in K_\eta(\rho)$.
--
--   This is the complex analogue of the classical second-moment asymptotics, without the cycle conditioning; the paper derives the conditioned estimate (Proposition 5.7) from it.
--
--
--   Differences from the source:
--   - encoding: 𝔼_M[Z^{(2)}_{M,<ε}(β)] = (1 + O(1/n)) · R_n(β) → ∃ C, ∃ N₀, ∀ n ≥ N₀ with nd even: ‖𝔼_M Z^{(2)}_{M,<ε}(β) − R_n(β)‖ ≤ (C/n)‖R_n(β)‖; reason: definition of a (complex) factor 1 + O(1/n)
--   - reading: for every β ∈ K_η(ρ) and every 0 < ε ≤ ε₀, … (1 + O(1/n)) → C and N₀ chosen after ε and before β, so uniform over β ∈ K_η(ρ) and allowed to depend on d, η, ε; reason: the paper holds all parameters other than n fixed (p.11); uniformity in β is the stronger reading and the base convention (decision 4)
--   - encoding: √· in (129) → principal square root, Complex.cpow · (1/2); reason: the radicands are positive reals on K_η(ρ) for small ρ, where the principal root is the positive root
--   - reading: Z^{(2)}_{M,<ε} in (129), the symbol of p.12 (σ¹, σ² ∈ Σ_n(ε), |R(σ¹,σ²)| < ε), while Lemma B.1 (p.67) represents it as a sum over type vectors with ‖α − ¼·1‖∞ < ε → `cmZ2lt` (the p.12 definition); reason: the theorem uses the paper's named symbol; both windows are neighbourhoods of α★ = ¼·1 of size comparable to ε, nested up to a constant factor in ε, and (129) does not depend on ε
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem B.5, eq. (129), p.73; notation N, p, q, h, δ₂, K_η(ρ), Appendix B, p.66; Z^{(2)}_{M,<ε}, Section 3.1, p.12

import Mathlib
import Definitions.Def_AFIsingKS_cmZ
import Definitions.Def_AFIsingKS_Supplement_secondMomentMain

open scoped Classical
open Set

namespace AFIsingKS.Supplement

/-- Theorem B.5 (Unconditioned second moment; Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held
version, sha256 2a07c158…), eq. (129), p.73): fix `0 < η < 1`; there are `ρ = ρ(d, η) > 0` and
`ε₀ = ε₀(d, η) > 0` such that for every `β ∈ K_η(ρ)` and every `0 < ε ≤ ε₀`,
`𝔼_M[Z^{(2)}_{M,<ε}(β)] = (1 + O(1/n)) · 4^n (h/4)^{N/2} √h / √((d(p−1)+2)(d(q−1)+2)) · 1/√(1 − (d−1)δ₂)`.

**Formalization Note.** `1 + O(1/n)` is stated as: there are `C` and `N₀` with
`‖𝔼_M Z^{(2)}_{M,<ε}(β) − R_n(β)‖ ≤ (C/n) ‖R_n(β)‖` for all `n ≥ N₀` with `nd` even, uniformly in
`β ∈ K_η(ρ)`; `C` and `N₀` may depend on the fixed `ε` (and on `d, η`), per the paper's convention (p.11)
that all other parameters are held fixed as `n → ∞`. `Z^{(2)}_{M,<ε}` is the base `cmZ2lt` of p.12, with
`β̄` on the second replica; `R_n(β)` is `secondMomentMain d n β`. -/
theorem theorem_B_5 (d : ℕ) (hd : 3 ≤ d) (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, Even (n * d) → ∀ β ∈ Keta d η ρ,
        ‖cmE (fun M : Matching n d => cmZ2lt ε M β) - secondMomentMain d n β‖ ≤
          C / n * ‖secondMomentMain d n β‖ := by sorry

end AFIsingKS.Supplement
