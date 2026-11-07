-- Prove2me | Theorems.Thm_ApproxGKR_completeness_C_2
-- name    : ApproxGKR.completeness_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:37.6912+00:00
-- url     : https://prove2.me/theorems/067b5685-fbc8-46ee-9183-28caa30b98ed
-- title:
--   §C.2 — completeness of approximate GKR for every challenge sequence
-- statement:
--   Let the extensions be admissible (individual degree at most $\delta$, agreement on the grid, $\|\cdot\|_1\le B_W$), let every exact gate value have modulus at most $B_V$, let $0<\Delta_0\le1$, $N\ge1$, and suppose $|y-C(x)|\le\Delta_0$. Let the prover send, at every layer and round, a polynomial $p_j$ of degree at most $D$ with
--   $$\big|[X^a]p_j-[X^a]q_j\big|\le\frac{\Delta_0}{h(D+1)}\qquad(0\le a\le D),$$
--   where $q_j$ is the true round polynomial given the earlier coins, and claimed evaluations within $\Delta_0$ of $\widetilde V_{i+1}(u_i)$ and $\widetilde V_{i+1}(v_i)$. Then for every verifier implementation whose computations have error at most $\Delta_0$ and for **every** coin tuple, the protocol accepts: all magnitude checks pass and every computed residual is within its tolerance ($6\Delta_0$, $(K+3)\Delta_0$, $4\Delta_0$).
--
--   This is the completeness half of Theorem C.1: acceptance with probability one, for any choice of challenges.
--
--   Differences from the source:
--   - generalization: the paper's verifier, whose computations have error at most ∆₀ → every verifier implementation within ∆₀; reason: the paper's verifier is one of them
--   - generalization: N the power of two of (C.17) → any N ≥ 1; reason: completeness does not use N
--   - generalization: the honest prover of p.32 → any prover meeting the honest accuracy bounds of p.32; reason: the honest prover meets them
--   - reading: coefficient error ∆₀/[h(D + 1)] (p.32) and "total coefficient error … ∆0/h" (p.35) → the per-coefficient bound ∆₀/[h(D + 1)] of p.32; reason: the two agree (D + 1 coefficients); the completeness accounting uses p.32's form
--   - encoding: finite-precision messages → exact complex polynomials and numbers; reason: encodings are the goal theorem's business; the analysis here is on values
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.2, pp.35–36; §C.1, p.32

import Mathlib
import Definitions.Def_ApproxGKR_AbsAccepts

namespace ApproxGKR

/-- **Completeness of approximate GKR for every challenge sequence** (§C.2, pp.35–36).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.2, pp.35–36: "These message bounds imply acceptance for every challenge
sequence." "All honest messages also meet the magnitude bounds in Equation (C.7), so every check
accepts, regardless of the challenges." The honest prover is the one of p.32: "Fix `0 < ∆0 ≤ 1`.
The honest prover computes every round coefficient within `∆0/[h(D + 1)]` and every claimed value
of `Ṽi+1` within `∆0`."

Let the extensions be admissible (`degree ≤ δ` per variable, agreement on the grid, `‖·‖₁ ≤ B_W`),
let every gate value have modulus at most `B_V`, let `0 < ∆₀ ≤ 1` and `|y − C(x)| ≤ ∆₀`. Let the
prover send round polynomials of degree at most `D` whose coefficients `[X^a]p_j`, `0 ≤ a ≤ D`, are
within `∆₀/[h(D + 1)]` of those of the true round polynomial `q_j`, and claimed evaluations within
`∆₀` of `Ṽᵢ₊₁(uᵢ)`, `Ṽᵢ₊₁(vᵢ)`. Then for every verifier implementation with errors at most `∆₀`
and **every** coin tuple, the abstract protocol accepts (including all magnitude checks).

**Formalization Note** Messages are exact complex numbers and polynomials (the encodings are the
business of the goal theorem); the verifier's computations are arbitrary functions of the coins
within `∆₀` of the exact quantities, which covers every implementation. `N ≥ 1` is arbitrary. -/
theorem completeness_C_2 (C : LayeredCircuit) (δ BV BW : ℕ) (ext : ExtFamily C)
    (x : InputList) (y : ℂ) (N : ℕ) (Δ₀ : ℝ) (P : AbsProver C N) (V : AbsVerifier C N)
    (hBV : 1 ≤ BV) (hBW : 1 ≤ BW)
    (hext : ∀ i < C.L, ∀ ty, IsAdmissibleExt C δ BW i ty (ext i ty))
    (hval : GateBound C x BV) (hN : 1 ≤ N) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1)
    (hy : ‖y - output C x‖ ≤ Δ₀)
    (hdeg : ∀ (c : Coins C N) (i j : ℕ), i < C.L → 1 ≤ j → j ≤ C.ki i →
      (P.poly i j c).natDegree ≤ C.Dpar δ)
    (hcoef : ∀ (c : Coins C N) (i j a : ℕ), i < C.L → 1 ≤ j → j ≤ C.ki i → a ≤ C.Dpar δ →
      ‖(P.poly i j c).coeff a - (roundPoly ext x c i j).coeff a‖ ≤
        Δ₀ / ((C.h : ℝ) * (C.Dpar δ + 1)))
    (hclaims : ∀ (c : Coins C N) (i : ℕ), i < C.L →
      ‖(P.claims i c).1 - MvPolynomial.eval (uPt c i) (Vt C x (i + 1))‖ ≤ Δ₀ ∧
      ‖(P.claims i c).2 - MvPolynomial.eval (vPt c i) (Vt C x (i + 1))‖ ≤ Δ₀)
    (hV : V.Within P ext x y Δ₀) :
    ∀ c : Coins C N, AbsAccepts P V y δ BV BW Δ₀ c := by sorry

end ApproxGKR
