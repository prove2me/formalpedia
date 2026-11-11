-- Prove2me | Theorems.Thm_DataDepProb_Discrete_proposition_C_1
-- name    : DataDepProb.Discrete.proposition_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:12:40.346911+00:00
-- url     : https://prove2.me/theorems/a89e3daf-2ddc-46d8-ac9e-3585a136b750
-- title:
--   Proposition C.1 — the penalized projection to duality gap $\tau$ in $O(d\log^3(2+d(1+\eta+\lambda)/\tau))$ operations and $O(d)$ space
-- statement:
--   Let $\eta>0$, $\lambda\ge0$ and $0<\tau\le1$, and let $q^+=\mathrm{MW}_\eta(q,f,b)$, $e=e_s$ be the inputs of Appendix C. For $A_s(p)=\mathrm{KL}(p\|q^+)+\lambda P_s(p)$, $P_s(p)=8H(p-e_s)^2$, one can compute $\hat p\in\tilde\Delta_d$ whose duality gap satisfies
--   $$\max_{w\in\tilde\Delta_d}\langle\nabla A_s(\hat p),\hat p-w\rangle\le\tau$$
--   using $O(d\log^3(2+d(1+\eta+\lambda)/\tau))$ operations and $O(d)$ space. In particular, if $\eta$, $\lambda$ and $\tau^{-1}$ are polynomially bounded in $nd$, the computation takes $O(d\log^3(nd))$ operations.
--
--   Formally: one admissible oracle-free program and one constant $C$ such that, with $d$ in pointer register $0$ and $\eta,\lambda,\tau,q^+,e$ in real memory from cell $0$, every run halts within $C\,d\log^3(2+d(1+\eta+\lambda)/\tau)$ steps, writes at most $C\,d$ memory cells, and leaves $\hat p$ in real cells $0,\dots,d-1$; and for every polynomial bound $c(nd)^k$ there is $C'$ with running time at most $C'd\log^3(nd)$ for the same program.
--
--   Differences from the source:
--   - reading: "one can compute … using $O(\cdot)$ operations and $O(d)$ space" → ∃ program (`Admissible`, `OracleFree`) ∃ $C>0$: `HaltsWithin` the operation bound, `SpaceWithin (C * d)` (distinct real and integer memory cells written), output in $\tilde\Delta_d$ with the gap bound; reason: the machine reading of the mission; registers are a constant of the program.
--   - reading: "polynomially bounded in $nd$" → ∀ $c$ ∀ $k$ ∃ $C'>0$: if $\eta,\lambda,1/\tau\le c(nd)^k$ (with $e=e_s$, $s\in[d]^n$) then `HaltsWithin (C' * d * log(nd)^3)`; reason: the constant of the "In particular" may depend on the polynomial only.
--   - reading: $n,d$ in the "In particular" clause → $n\ge1$, $d\ge2$; reason: the standing assumptions of Theorem 1.1, where the clause is used; for $nd=1$ the bound $\log^3(nd)=0$ is meaningless.
--   - reading: the standing inputs of Appendix C → `ProjInput η qplus e`; reason: Appendix C's section assumption.
--   - encoding: $\langle\nabla A_s(\hat p),\hat p-w\rangle$ → `fderiv ℝ (objA lam qplus e) p̂ (p̂ - w)`; reason: the gradient pairing is the Fréchet derivative.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 37, Proposition C.1 (proof p. 39, Algorithm 4)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_ScalarReduction
import Definitions.Def_DataDepProb_Discrete_Machine

namespace DataDepProb.Discrete

/-- Proposition C.1 (computing the penalized projection, p. 37). Let `η > 0`, `λ ≥ 0`,
`0 < τ ≤ 1`, and let `q⁺ = MW_η(q, f, b)`, `e = e_s` be the inputs of Appendix C. For
`A_s(p) = KL(p‖q⁺) + λP_s(p)`, `P_s(p) = 8H(p − e_s)²`, one can compute `p̂ ∈ ∆̃_d` with duality gap
`max_{w ∈ ∆̃_d} ⟨∇A_s(p̂), p̂ − w⟩ ≤ τ` using `O(d log³(2 + d(1 + η + λ)/τ))` operations and `O(d)`
space: one fixed deterministic oracle-free program with rational literals and one constant `C`
such that the run on input (`d` in pointer register `0`; real memory
`η, λ, τ, q⁺(0), …, q⁺(d − 1), e(0), …, e(d − 1)` from cell `0`) halts after at most
`C·d·log³(2 + d(1 + η + λ)/τ)` steps, writes at most `C·d` memory cells, and leaves `p̂` in real
memory cells `0, …, d − 1`. In particular, if `η`, `λ` and `τ⁻¹` are bounded by a polynomial
`c(nd)^k` in `nd` (`e = e_s`, `s ∈ [d]^n`, `n ≥ 1`, `d ≥ 2`), the same program takes
`O(d log³(nd))` operations, with a constant depending only on `c` and `k`. -/
theorem proposition_C_1 :
    ∃ P : Program, Admissible P ∧ OracleFree P ∧ ∃ C : ℝ, 0 < C ∧
      (∀ (d : ℕ) (η lam τ : ℝ) (qplus e : Fin d → ℝ),
        0 < η → 0 ≤ lam → 0 < τ → τ ≤ 1 → ProjInput η qplus e →
        HaltsWithin P detG zeroTape
            (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e))
            (C * d * Real.log (2 + d * (1 + η + lam) / τ) ^ 3) ∧
        SpaceWithin P detG zeroTape
            (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e)) (C * d) ∧
        outVec P detG zeroTape
            (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e)) d
          ∈ truncSimplex d ∧
        ∀ w ∈ truncSimplex d,
          fderiv ℝ (objA lam qplus e)
              (outVec P detG zeroTape
                (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e)) d)
              (outVec P detG zeroTape
                (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e)) d - w)
            ≤ τ) ∧
      ∀ (c : ℝ) (k : ℕ), ∃ C' : ℝ, 0 < C' ∧
        ∀ (n d : ℕ) (η lam τ : ℝ) (qplus e : Fin d → ℝ) (s : Fin n → Fin d),
          1 ≤ n → 2 ≤ d → 0 < η → 0 ≤ lam → 0 < τ → τ ≤ 1 → ProjInput η qplus e →
          e = eInit s →
          η ≤ c * ((n : ℝ) * d) ^ k → lam ≤ c * ((n : ℝ) * d) ^ k → 1 / τ ≤ c * ((n : ℝ) * d) ^ k →
          HaltsWithin P detG zeroTape
            (initState [(d : ℤ)] [] ([η, lam, τ] ++ List.ofFn qplus ++ List.ofFn e))
            (C' * d * Real.log ((n : ℝ) * d) ^ 3) := by sorry

end DataDepProb.Discrete
