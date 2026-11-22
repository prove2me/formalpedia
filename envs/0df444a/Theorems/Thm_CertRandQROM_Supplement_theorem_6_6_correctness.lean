-- Prove2me | Theorems.Thm_CertRandQROM_Supplement_theorem_6_6_correctness
-- name    : CertRandQROM.Supplement.theorem_6_6_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:47:43.196355+00:00
-- url     : https://prove2.me/theorems/1929b178-e7f3-4cee-a98f-8dc0e73de21d
-- title:
--   Theorem 6.6 (Correctness) — the honest prover of Construction 6.2 is rejected with negligible probability
-- statement:
--   Let $C_\lambda\subseteq\Sigma_\lambda^{n}$ be the folded Reed–Solomon code of §5.2 ($q=2^{2\lfloor\log\lambda\rfloor}$, $\Sigma_\lambda=\mathbb F_q^m$, $n=2^{\lfloor\log\lambda\rfloor}-1$), and let $H:[n]\times\Sigma_\lambda\to\{0,1\}$ be the $p$-biased random oracle: the values $H(i,x)$ are independent with $\Pr[H(i,x)=1]=p$, $p$ the power of $1/2$ in $(\tfrac1{80\sqrt n},\tfrac1{40\sqrt n}]$.
--   In Construction 6.2 the prover prepares, for each $i$, the uniform superposition $|\phi_i\rangle$ over $\{e:H(i,e)=0\}$ (at most $\lambda$ trials, aborting with $\pi=\bot$ if some coordinate fails), applies the quantum Fourier transform to $|\psi\rangle\propto\sum_{x\in C}|x\rangle$ and to $|\phi\rangle=\bigotimes_i|\phi_i\rangle$, adds the first register into the second, subtracts $\mathrm{Decode}_{C^\perp}$ of the second register from the first, applies the inverse transform to the second register and measures it to obtain $\pi$. The verifier accepts $\pi=x$ when $x\in C$ and $H(i,x_i)=0$ for all $i$.
--
--   **Theorem.** Construction 6.2 satisfies correctness: the function
--
--   $$
--   \lambda\ \longmapsto\ \Pr_{H}\Big[\mathrm{Verify}^H(1^\lambda,1^{h_\infty},\pi)=\bot\ :\ \pi\leftarrow\mathrm{Prove}^H(1^\lambda,1^{h_\infty})\Big]
--   $$
--
--   is negligible, the probability being over the oracle $H$ and the prover's internal randomness.
--
--   Correctness is the completeness half of the certified-randomness protocol: an honest quantum device passes the test. Together with the published certifiable-min-entropy goal it gives Theorem 6.3.
--
--   **Formalization Note** The rejection probability for a fixed oracle is `honestRejProb`, an exact finite expression (abort probability of step 1 plus the Born-rule weight of the incorrect outcomes); it is averaged over the oracle with the published `ErasureQTanner.noisyExp` at bias `biasP n`. The fields and generators are parameters, as in the published goal.
--
--   Differences from the source:
--   - generalization: the field F_{q(λ)} with q(λ) = 2^{2⌊log λ⌋} and an arbitrary generator γ(λ) of F_q^* → any field family F with |F λ| = 2^{2⌊log₂ λ⌋} and any γ λ of order |F λ| − 1, for λ ≥ 2; reason: every field with q elements is isomorphic to F_q; the paper's choice is one instance (same parameters as the published goal)
--   - encoding: FRS evaluation points γ^{jm+1}, …, γ^{jm+m}; log λ → the published CertRandQROM.code (TFNPRom.foldedRS, points γ^{jm}, …, γ^{jm+m−1}); Nat.log 2; reason: the two codes are equal as sets (proved in the base sanity file); logarithms are base 2
--   - encoding: the probability over H and over the prover's internal randomness (step-1 trials, final measurement) → ErasureQTanner.noisyExp (biasP n) of honestRejProb, the exact rejection probability given H = h; reason: finite sums; given that step 1 succeeds the state is |φ⟩ whatever the trial history, so the abort probability is 1 − Π_i (1 − (1 − |T_i|/|Σ|)^λ) and the Born rule gives the rest
--   - encoding: QFT_Σ "given in [YZ24, Section 2.2]" (footnote 6) → the transform |x⟩ ↦ q^{−nm/2} Σ_y (−1)^{Tr(x·y)} |y⟩ with Tr(a) = Σ_{i<log₂ q} a^{2^i} the absolute trace F_q → F_2 and x·y the unfolded dot product; reason: this is the cited definition in characteristic 2 (q = 2^{2⌊log λ⌋}); the n-fold tensor power of the blockwise transform is the transform over Σ^n because Tr is additive
--   - encoding: Decode_{C⊥}: run GRSUniqueDecode with decoding radius τ = ⌊(k+1)/2⌋; return its codeword, or 0 on ⊥ (p.25) → decodeDual C τ z: a dual codeword within unfolded Hamming distance τ of z if one exists (Classical.choose), else 0; reason: the specification of GRSUniqueDecode on p.22; the codeword is unique for C_λ since d_min(C⊥) = k + 2 > 2τ (p.26), so no hypothesis on the decoder is assumed
--   - encoding: "For any h∞ = h∞(λ)" (Definition 6.1, Correctness) → one statement in λ; reason: Prove and Verify of Construction 6.2 ignore the input 1^{h∞}
--   - encoding: negl(λ) → CommitOpen.Benign.Negligible (∀ c, eventually |ν(λ)| ≤ λ^{−c}); reason: standard definition, the one used by the published goal
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Theorem 6.6 (Correctness), p.31 (PDF p.33); Definition 6.1, Correctness, p.28 (PDF p.30); Construction 6.2, pp.28–29 (PDF pp.30–31)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_CertRandQROM_biasP
import Definitions.Def_CertRandQROM_code
import Definitions.Def_CertRandQROM_Supplement_honestRejProb

set_option autoImplicit false

namespace CertRandQROM.Supplement

/-- **Theorem 6.6 (Correctness)** (Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal,
*Unconditional Certified Randomness without Structure*, arXiv:2608.31112 (sha256 b75095a2…),
p.31): Construction 6.2 satisfies correctness (Definition 6.1, p.28):
`Pr_H[Verify^H(1^λ, 1^{h∞}, π) = ⊥ : π ← Prove^H(1^λ, 1^{h∞})] ≤ negl(λ)`.

The probability is over the `p`-biased oracle `H ∼ H` on `[n] × Σ` (`p = biasP n`, the
published `ErasureQTanner.noisyExp`, `true` = value `1` with probability `p`) and over the
prover's internal randomness (`honestRejProb` is the exact conditional rejection probability
given `H = h`).

**Formalization Note** The code is the §5.2 family for any field family with
`|F λ| = 2^{2⌊log₂ λ⌋}` and any generators `γ λ` with `orderOf (γ λ) = |F λ| − 1` (for `λ ≥ 2`),
exactly as in the published goal `CertRandQROM.theorem_7_1_certifiable_min_entropy`.
"Negligible" is `CommitOpen.Benign.Negligible`. `Prove` and `Verify` ignore `1^{h∞}`, so the
statement for every `h∞(λ)` is this one statement in `λ`. -/
theorem theorem_6_6_correctness (F : ℕ → Type) [∀ l, Field (F l)]
    [∀ l, Fintype (F l)] [∀ l, DecidableEq (F l)]
    (hF : ∀ l, 2 ≤ l → Fintype.card (F l) = 2 ^ (2 * Nat.log 2 l))
    (γ : ∀ l, F l) (hγ : ∀ l, 2 ≤ l → orderOf (γ l) = Fintype.card (F l) - 1) :
    CommitOpen.Benign.Negligible fun l =>
      ErasureQTanner.noisyExp (CertRandQROM.biasP (CertRandQROM.nPar F l))
        (fun h => honestRejProb F γ l h) := by sorry

end CertRandQROM.Supplement
