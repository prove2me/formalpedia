-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_C_4
-- name    : DataDepProb.Discrete.lemma_C_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:12:35.651873+00:00
-- url     : https://prove2.me/theorems/ad4b5959-af8b-461b-b60f-611d1304c4c9
-- title:
--   Lemma C.4 — $p_\theta$ to $\ell_1$ accuracy $\varepsilon_1$ in $O(d\log(N/\alpha)\log(1/\alpha))$ operations
-- statement:
--   For the inputs of Appendix C ($\eta>0$, $\lambda\ge0$, $q^+=\mathrm{MW}_\eta(q,f,b)$, $e=e_s$), for $0\le\theta\le\Theta$ and $0<\varepsilon_1\le1/2$, one can compute $\hat p\in\tilde\Delta_d$ with $\|\hat p-p_\theta\|_1\le\varepsilon_1$ in
--   $$O\big(d\log(N/\alpha)\log(1/\alpha)\big)\ \text{operations},\qquad \alpha=\frac{\varepsilon_1}{5d},\quad N=\Lambda+\eta+\Theta\Gamma .$$
--   Formally: there are one admissible oracle-free program and one constant $C$ such that, for all such inputs, the run with $d$ in pointer register $0$ and $\theta,\eta,\lambda,\varepsilon_1,q^+(0),\dots,q^+(d-1),e(0),\dots,e(d-1)$ in real memory from cell $0$ halts within $C\,d\log(N/\alpha)\log(1/\alpha)$ steps and leaves $\hat p$ in real cells $0,\dots,d-1$.
--
--   Differences from the source:
--   - reading: "one can compute … in $O(\cdot)$ operations" → ∃ program (`Admissible`, `OracleFree`) ∃ $C>0$, uniform over $d$ and all inputs, with the input layout above and `HaltsWithin`; reason: the machine reading of the mission.
--   - reading: the standing inputs of Appendix C → `ProjInput η qplus e`, `0 < η`, `0 ≤ lam`; reason: Appendix C's section assumption ($\lambda\ge0$ from Proposition C.1).
--   - encoding: $p_\theta$ → `pTheta`; reason: the unique minimizer.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 38, Lemma C.4 (proof pp. 40–41)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_ScalarReduction
import Definitions.Def_DataDepProb_Discrete_Machine

namespace DataDepProb.Discrete

/-- Lemma C.4 (computing `p_θ`, p. 38). For the inputs of Appendix C (`η > 0`, `λ ≥ 0`,
`q⁺ = MW_η(q, f, b)`, `e = e_s`), `0 ≤ θ ≤ Θ = 16λ log(1 + d)` and `0 < ε₁ ≤ 1/2`, one can compute
`p̂ ∈ ∆̃_d` with `‖p̂ − p_θ‖₁ ≤ ε₁` in `O(d log(N/α) log(1/α))` operations, `α = ε₁/(5d)`,
`N = Λ + η + ΘΓ`: one fixed deterministic oracle-free program with rational literals and one
constant `C` such that the run on input (`d` in pointer register `0`; real memory
`θ, η, λ, ε₁, q⁺(0), …, q⁺(d − 1), e(0), …, e(d − 1)` from cell `0`) halts after at most
`C·d·log(N/α)·log(1/α)` steps with `p̂` in real memory cells `0, …, d − 1`. -/
theorem lemma_C_4 :
    ∃ P : Program, Admissible P ∧ OracleFree P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (η lam θ ε₁ : ℝ) (qplus e : Fin d → ℝ),
        0 < η → 0 ≤ lam → ProjInput η qplus e → 0 ≤ θ → θ ≤ ThetaC lam d →
        0 < ε₁ → ε₁ ≤ 1 / 2 →
        HaltsWithin P detG zeroTape
            (initState [(d : ℤ)] [] ([θ, η, lam, ε₁] ++ List.ofFn qplus ++ List.ofFn e))
            (C * d * Real.log ((LambdaC d + η + ThetaC lam d * gammaC d) / (ε₁ / (5 * d)))
              * Real.log (1 / (ε₁ / (5 * d)))) ∧
        outVec P detG zeroTape
            (initState [(d : ℤ)] [] ([θ, η, lam, ε₁] ++ List.ofFn qplus ++ List.ofFn e)) d
          ∈ truncSimplex d ∧
        l1dist (outVec P detG zeroTape
            (initState [(d : ℤ)] [] ([θ, η, lam, ε₁] ++ List.ofFn qplus ++ List.ofFn e)) d)
          (pTheta qplus e θ) ≤ ε₁ := by sorry

end DataDepProb.Discrete
