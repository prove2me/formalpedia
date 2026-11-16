-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_Supplement_theorem_6_1
-- name    : CKKSPrecision.FourierUnits.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:27:28.016725+00:00
-- url     : https://prove2.me/theorems/f8303375-5e22-4a16-9514-db0d592e40da
-- title:
--   Theorem 6.1 — allocation bound for a general circuit
-- statement:
--   For every power-of-two slot dimension $r\ge1$, fix a finite CKKS circuit with its complex inputs and public constants, odd input moduli, odd rescaling divisors greater than one, positive rational input and plaintext scales, and rational nonnegative magnitude and primitive error bounds as in §6.1. Moduli and scales follow §7.1. Fix required slots $S$ and rational thresholds $\varepsilon_j$. Let $W_j(t)=c_jt^{s_j}$, where each $c_j>0$ is rational and $s_j\in\{-1,1\}$, and form the Laurent error bounds by the exact rewritten rules. Define $F,T,J$ by (13)–(15), averaging over all $r$ slots.
--
--   Algorithm 1 terminates, with endpoint inclusion retained, and returns
--   $$
--   I=\log_2 J,\qquad
--   J=\{t\ge1:F(t)<T,\ E_{\mathrm{out},j}(t)\le\varepsilon_j\ (j\in S)\}.
--   $$
--   Termination is expressed by existence of finite root/sign data denoting exactly $J$: every cut is a root of a nonzero rational polynomial obtained by clearing a defining Laurent constraint, with $X-1$ also included for the domain boundary. The set $J$ is an interval, allowing the empty, singleton and unbounded cases. If $J$ is nonempty, its lower endpoint is algebraic over $\mathbb Q$, and its upper endpoint is algebraic when bounded above.
--
--   For every $t\in J$, every integral unit $u\in R^\times$ satisfying
--   $$
--   |\sigma_j(u)|\le W_j(t)\quad(0\le j<r),
--   $$
--   and every execution with $p=u$ on the joint primitive-error event and with the public automorphism corrections specified in §7.1, centered decryption returns the entire computed $M_{\mathrm{out}}$. Moreover,
--   $$
--   |\widehat x_{\mathrm{out},j}-x_{\mathrm{out},j}|\le\varepsilon_j\qquad(j\in S).
--   $$
--   The joint event is deterministic; there is no probability or independence assertion. This companion theorem supplies the circuit-level allocation guarantee and is not used in the proof of the published Fourier-construction goal.
--
--   Differences from the source:
--   - encoding: the CKKS cyclotomic ring and selected embeddings in power-of-two dimension, with ciphertext components in R_Q → the published field and integral subalgebra, Fin r slots, an explicit power-of-two hypothesis and integral representatives with congruence modulo Q; reason: these are the same ring, cyclic embedding order and quotient classes, including r=1; field expressions carry explicit integral-ring membership and the operations choose the prescribed representatives
--   - generalization: weights t^{s_j} or Gamma t^{s_j} with a common positive rational Gamma for the fixed two-level groups → weights c_j t^{s_j} with arbitrary positive rational c_j and arbitrary signs in {-1,1} for each slot; reason: both source cases are included; the same nonnegative Laurent propagation, convexity and rational root isolation apply
--   - encoding: Algorithm 1 terminates using exact root isolation, sign determination and endpoint comparisons → the literal finite node and intersection loops use the exact-set Solve interface, with existence of a finite polynomial-root/sign certificate denoting J; reason: finite cuts with finite point and cell flags retain all endpoint inclusion and certify finite exact solution data without assuming an unimplemented solver is computable
--   - encoding: finite endpoints of an interval which may be empty or unbounded → sInf J is algebraic when J is nonempty and sSup J is algebraic when additionally bounded above; reason: J is bounded below by 1; these guards exclude the default values of real infima and suprema on undefined cases
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), p. 11 (PDF p. 13), Theorem 6.1, (13)–(15); Algorithm 1 and proof p. 12 (PDF p. 14); §§7.1–7.2 and Appendix B.

import Definitions.Def_CKKSPrecision_FourierUnits_Supplement_allocation_model

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits.Supplement

theorem theorem_6_1 (r : ℕ+) (hr : ∃ k : ℕ, (r : ℕ) = 2 ^ k)
    (w : Weights r) (c : Circuit r) (hc : ValidCircuit w c) (req : Requirements r) :
    let j := feasible w c req
    algorithm1 w c req = logTwo '' j ∧
      (∃ cert : RangeCertificate,
        cert.Valid (boundaryPolynomials w c req) ∧ cert.denotes = j) ∧
      Set.OrdConnected j ∧
      (j.Nonempty → IsAlgebraic ℚ (sInf j) ∧ (BddAbove j → IsAlgebraic ℚ (sSup j))) ∧
      ∀ t ∈ j, ∀ u : (R (conductor r))ˣ,
        (∀ k, ‖sigma (u.val : Scalar r) k‖ ≤ weight w t k) →
        ∀ (s : Scalar r) (noise : ℕ → Noise r),
          JointExecution w c (u.val : Scalar r) s noise →
          Successful w c req (u.val : Scalar r) s noise := by sorry

end CKKSPrecision.FourierUnits.Supplement
