-- Prove2me | Theorems.Thm_DiagLinesLDT_Supplement_theorem_10_1
-- name    : DiagLinesLDT.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:22:03.473201+00:00
-- url     : https://prove2.me/theorems/f7e66c43-f572-4359-9385-7c7d59e624ef
-- title:
--   Theorem 10.1 — quantum soundness of the total-degree diagonal line-versus-point test with $C_0=2000000$
-- statement:
--   Let $\mathbb F_q$ be any finite field, let $m\ge1$ and $d\ge0$, and let
--
--   $$
--   (|\psi\rangle,A^{\mathrm A},L^{\mathrm A},A^{\mathrm B},L^{\mathrm B})
--   $$
--
--   be a projective strategy accepted by the degree-$d$ total-degree diagonal line-versus-point test with probability at least $1-\varepsilon$, where $0\le\varepsilon\le1$. For every real $k\ge md$, put
--
--   $$
--   c_0=\frac1{40000},\qquad
--   \nu_{\mathrm{tot}}=2000000(k+1)^2m^4\left(\varepsilon^{c_0}+\left(\frac dq\right)^{c_0}+e^{-k/(2560000m^2)}\right).
--   $$
--
--   Then there are projective measurements $G^{\mathrm A},G^{\mathrm B}\in\operatorname{TotPolyMeas}(m,q,d)$ such that all three of the following disagreement probabilities are at most $\nu_{\mathrm{tot}}$:
--
--   1. averaged over $u\in\mathbb F_q^m$, Alice's point outcome $A^{\mathrm A,u}$ disagrees with the value at $u$ of Bob's polynomial outcome $G^{\mathrm B}$;
--   2. averaged over $u\in\mathbb F_q^m$, Bob's point outcome $A^{\mathrm B,u}$ disagrees with the value at $u$ of Alice's polynomial outcome $G^{\mathrm A}$;
--   3. Alice's and Bob's full polynomial labels from $G^{\mathrm A}$ and $G^{\mathrm B}$ disagree.
--
--   Equivalently, in the paper's notation,
--
--   $$
--   A^{\mathrm A,u}_a\otimes I\simeq_{\nu_{\mathrm{tot}}}I\otimes G^{\mathrm B}_{[g(u)=a]},\qquad
--   I\otimes A^{\mathrm B,u}_a\simeq_{\nu_{\mathrm{tot}}}G^{\mathrm A}_{[g(u)=a]}\otimes I,
--   $$
--
--   and $G^{\mathrm A}_g\otimes I\simeq_{\nu_{\mathrm{tot}}}I\otimes G^{\mathrm B}_g$.
--
--   This is the paper's soundness theorem for total degree: high acceptance forces both provers' point measurements to be jointly explained, up to the explicit error, by consistent global polynomials of total degree at most $d$.
--
--   **Formalization Note** Finite field types encode all prime powers $q$. The parameter $k$ remains real. The literal sampler includes $v=0$ and singleton lines, and no hypothesis such as $q>md$ or $q>6md$ is imposed. The three $\simeq$ relations are expanded as their probability-style disagreement sums.
--
--   Differences from the source:
--   - generalization: the theorem text leaves $C_0$ as an unspecified universal constant → Lean fixes $C_0=2000000$; reason: the proof on p.35 supplies this witness, yielding the source theorem with an explicit quantitative constant
--   - encoding: a prime power $q$ and finite-dimensional complex Hilbert spaces → an arbitrary finite field type $F$ with $q=|F|$ and matrix spaces $\mathbb C^{\iota_A},\mathbb C^{\iota_B}$; reason: every finite field has prime-power cardinality and every finite-dimensional complex Hilbert space admits such coordinates
--   - encoding: points in $\mathbb F_q^m$, affine-line questions, function answers on a line, and projective measurements → points as `Fin m → F`, line questions as point sets, answers as dependent functions on those sets, and PVMs as Hermitian idempotent matrix families; reason: these are coordinate and bundling conventions that preserve exactly the source questions, answers, and strategies
--   - encoding: functions whose unique reduced representatives have total degree at most $d$ → functions admitting a multivariate representative of total degree at most $d$; reason: reduction modulo $X_i^q-X_i$ preserves the function and cannot increase total degree, so the outcome classes coincide
--   - encoding: the notation $\simeq_{\nu_{\mathrm{tot}}}$ → explicit averaged sums of the real parts of $\langle\psi|M_a\otimes N_b|\psi\rangle$ over unequal outcomes; reason: tensor products of projectors have real nonnegative expectations, so taking the real part preserves exactly the probability-style consistency convention of §9
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Theorem 10.1, p.27, with C₀ = 2000000 from its proof, p.35

import Mathlib
import Definitions.Def_DiagLinesLDT_Supplement_TotalDegreeStrategy

namespace DiagLinesLDT.Supplement

set_option autoImplicit false

/-- Theorem 10.1 (Quantum soundness of the total-degree diagonal line-vs-point test), Zhao, Fu,
Yu, *The Role of Diagonal Lines in Quantum Low-Degree Testing*, STOC 2027 submission (PDF of
2026-11-03, sha256 831c30c6…), p.27, with the proof's explicit universal constant `C0 = 2000000`
from p.35.

For every finite field, every normalized projective strategy accepted with probability at least
`1-epsilon`, and every real `k >= m*d`, there are total-degree-at-most-`d` projective polynomial
measurements on both provers whose two cross-prover point-value inconsistency errors and their
polynomial-label inconsistency are at most `soundnessError q m d epsilon k`.

**Formalization Note** Finite fields encode the paper's prime-power `q`. Hilbert spaces are finite
coordinate spaces over `C`, matrices act on them, and Alice's tensor factor is left. `DiagDirection`
retains `v = 0`, so singleton queries occur literally. `TotalDegreeFunction` is the function-level
reduced-polynomial outcome class. The relation is the paper's averaged disagreement probability,
not an operator norm. The theorem keeps `k` real and imposes no `q > m*d` side condition. -/
theorem theorem_10_1 :
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F]
      (m d : ℕ) (hm : 0 < m) (epsilon k : ℝ),
      0 ≤ epsilon → epsilon ≤ 1 → (m * d : ℕ) ≤ k →
      ∀ (iotaA iotaB : Type*) [Fintype iotaA] [DecidableEq iotaA]
        [Fintype iotaB] [DecidableEq iotaB]
        (S : TotalDegreeStrategy F m d iotaA iotaB),
        S.IsProjective → 1 - epsilon ≤ totalDegreeAcc S →
        ∃ (GA : TotalDegreeFunction F m d → Matrix iotaA iotaA ℂ)
          (GB : TotalDegreeFunction F m d → Matrix iotaB iotaB ℂ),
          MIPRE.IsPVM GA ∧ MIPRE.IsPVM GB ∧
          DiagLinesLDT.uniformAvg (fun u : Fin m → F =>
            inconsistency S.state (fun a => S.pointA u a) (fun a => pointValue GB u a)) ≤
              soundnessError (Fintype.card F) m d epsilon k ∧
          DiagLinesLDT.uniformAvg (fun u : Fin m → F =>
            inconsistency S.state (fun a => pointValue GA u a) (fun a => S.pointB u a)) ≤
              soundnessError (Fintype.card F) m d epsilon k ∧
          inconsistency S.state GA GB ≤ soundnessError (Fintype.card F) m d epsilon k := by sorry

end DiagLinesLDT.Supplement
