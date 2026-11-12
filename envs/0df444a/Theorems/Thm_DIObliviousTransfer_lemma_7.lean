-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_7
-- name    : DIObliviousTransfer.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:08:05.012691+00:00
-- url     : https://prove2.me/theorems/91024665-4bad-442b-b616-01790cf7a857
-- title:
--   Lemma 7 — diagonal code masking
-- statement:
--   Put $\xi=6(0.047)-\log_2(64/63)>0.25$. Let $\rho_{\beta\Lambda E}$ be a subnormalized cq state with $\beta\in\mathbb F_{64}^m$ and $H_{\min}(\beta\mid\Lambda E)\ge km-b$, where $\Lambda$ is a classical label that selects a secret $u(\lambda)\in\mathbb F_{64}^q$. Sample $\sigma$ uniformly in $(\mathbb F_{64}^*)^m$ and $R$ uniformly in $B^\sigma_{u(\lambda)}$. Then
--   $$\big\|\rho_{\sigma,\beta+R,\Lambda E}-\rho_\sigma\otimes\tau_{km}\otimes\rho_{\Lambda E}\big\|_1\le2^{-(\xi m-b)/2}.$$
--
--   This masking bound gives choice hiding in the transfer and the source commitment.
--
--   Differences from the source:
--
--   - generalization: AG codes B = D = ev_P L(G), A = ev_P L(2G) on the Garcia–Stichtenoth tower over F₆₄ → any CodeFamily satisfying the conclusions of Lemmas 5 and 6 (CodeFamily.Spec); reason: Decision D15: the AG family satisfies the interface by Lemmas 5 and 6, so the statement specializes to the paper's
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
--   - encoding: a retained common classical label, included in E, that selects u and the cq state → side information Λ × E′ with a classical label Λ and u : Λ → F₆₄^q; the label-free case is Λ = Unit; reason: the lemma's last sentence; one statement covers both cases
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 7, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DIObliviousTransfer_Ltotal
import Definitions.Def_DIObliviousTransfer_maskedDiff

namespace DIObliviousTransfer

/-- **Lemma 7 (Diagonal code masking)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version,
sha256 8334c039…), p.26 (PDF p.28). With `ξ = 6(0.047) − log₂(64/63) > 0.25`: for a subnormalized
cq state `ρ_{βΛE}` on `F₆₄^m` with `H_min(β | ΛE) ≥ km − b`, an independent uniform diagonal
`σ ∈ (F₆₄^*)^m` and `R` uniform in `B^σ_{u(λ)}`,
`‖ρ_{σ,β+R,ΛE} − ρ_σ ⊗ τ_{km} ⊗ ρ_{ΛE}‖₁ ≤ 2^{−(ξm−b)/2}`, uniformly in the label-selected secret.

**Formalization Note** (decision D15). The code `B` is that of any `CodeFamily` satisfying the
interface of Lemmas 5–6, at an admissible length `m` and `1 ≤ q ≤ ⌊m/100⌋`; the AG family of the
paper is one. The label `Λ` is part of the side information. -/
theorem lemma_7 (C : CodeFamily) (hC : C.Spec) (m q : ℕ) (hm : IsAdmissible m) (hq1 : 1 ≤ q)
    (hq : q ≤ m / 100) {Λ E : Type} [Fintype Λ] [DecidableEq Λ] [Fintype E] [DecidableEq E]
    (ρ : (Fin m → F64) → Λ → Matrix E E ℂ) (hρ : IsSubCQ fun β => cqOp (ρ β))
    (u : Λ → Fin q → F64) (b : ℝ)
    (hH : (((kk * m : ℕ) : ℝ) - b : ℝ) ≤ Hmin (fun β => cqOp (ρ β))) :
    0.25 < 6 * (0.047 : ℝ) - Real.logb 2 (64 / 63) ∧
    WildeQIT.traceNorm (maskedDiff C m q ρ u) ≤
      (2 : ℝ) ^ (-(((6 * (0.047 : ℝ) - Real.logb 2 (64 / 63)) * m - b) / 2)) := by sorry

end DIObliviousTransfer
