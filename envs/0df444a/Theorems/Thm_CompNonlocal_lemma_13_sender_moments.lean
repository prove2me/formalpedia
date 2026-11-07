-- Prove2me | Theorems.Thm_CompNonlocal_lemma_13_sender_moments
-- name    : CompNonlocal.lemma_13_sender_moments
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:54.966222+00:00
-- url     : https://prove2.me/theorems/caa5b00c-3aaa-4505-98c4-90cb18486a52
-- title:
--   Lemma 13, pp.39–40 — moments of the sender observables
-- statement:
--   In the §8.1 preparation built from a certificate, let $r(T)$ be the Bloch vector of the prepared state (27) and $m_j$ the ideal outcome of measuring the sender observable $M_j$ of Eq. (28) on the sender state (each $m_j$ a separate measurement). For every transcript $t=(x,a)$ of positive probability,
--   $$\frac13\sum_j\mathbb E[r_j(T)m_j\mid T=t]=\frac23\langle r(t),w_{x,a}\rangle,\qquad\frac13\sum_j\mathbb E[m_j^2\mid T=t]\le\frac13,$$
--   and averaging over $T$,
--   $$\frac13\sum_j\mathbb E[r_j(T)m_j]=\frac{2\mathfrak a}3,\qquad\frac13\sum_j\mathbb E[m_j^2]\le\frac13, \tag{29}$$
--   with $w_{x,a}$ and $\mathfrak a$ as in Definition 13.
--
--   These moment bounds turn the alignment $\mathfrak a$ into small mean squared error for the sender's coordinate estimates.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Alice's algorithm A(x, ω_A) acts on her qubit → hypothesis 1 ≤ (c.A κ).nq: the honest Alice circuit reads at least one quantum-input wire; reason: in the circuit model a circuit may ignore its quantum input; the paper's A(x, ω_A) and the §8.1 receiver run Alice's circuit on her qubit
--   - encoding: E[r_j(T) m_j | T = t] and E[m_j^k | T = t] → r_j(t) · Tr(ω_{S|x} M_j) and Tr(ω_{S|x} M_j^k) (c.senderMoment); reason: r_j(T) is fixed given T and m_j is the spectral outcome of M_j on ω_{S|x} (proof, p.40)
--   - encoding: expectations over X and a ← p_X, conditional quantities w_{x,a}, ω_{S|x}, r(t) → sums over the question outcomes with the conditioning multiplied out (unnormalized branches), normalized only at outcomes of positive probability; reason: avoids junk values at probability-0 outcomes; the same numbers
--   - generalization: the §8.1 construction from the certificate of Theorem 6 (uniform QPT algorithms certifying ρ(v) with gap (25)), p.35 → the §8.1 receiver built from any Certificate whose honest Alice reads her qubit (no uniformity or gap hypothesis); reason: the proofs use only the circuit structure (Lemma 1, the singlet identity, 0 ⪯ F ⪯ I), not the gap or uniformity; the certificate of Theorem 6 is an instance
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 13, pp.39–40, Eq. (29)

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_prepProb
import Definitions.Def_CompNonlocal_Certificate_senderMoment
import Definitions.Def_CompNonlocal_Certificate_bobAccEffect
import Definitions.Def_CompNonlocal_Certificate_align
import Definitions.Def_CompNonlocal_blochVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- **Lemma 13 (Moments of the sender observables).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), pp.39–40: "Let r(T) be the Bloch vector of the prepared state defined in Equation (27),
and let m_j be the ideal outcome of measuring M_j on the sender state. Each m_j refers to a separate
measurement of the original state. For every transcript t = (x, a) of positive probability,
(1/3) Σ_j E[r_j(T)m_j | T = t] = (2/3)⟨r(t), w_{x,a}⟩, (1/3) Σ_j E[m_j² | T = t] ≤ 1/3. Averaging
over T gives (1/3) Σ_j E[r_j(T)m_j] = 2𝔞/3, (1/3) Σ_j E[m_j²] ≤ 1/3, (29) where w_{x,a} and 𝔞 are as
in Definition 13."

**Formalization Note** In the §8.1 preparation of a certificate `c` at `κ` (Alice's honest circuit
reading her qubit), `t = (x, z)` with `z` the complete record and `a = (c.A κ).clOut z` its answer;
`r(t)` is the Bloch vector of the normalized prepared state; `M_j` is `c.senderObs` (Eq. (28)), and
`E[m_j^k | T = t] = Tr(ω_{S|x} M_j^k) = c.senderMoment κ x a j k`, since `r_j(T)` is fixed given `T`.
`w_{x,a} = ½ blochVec(W_{x,a})` with `Pr[x] W_{x,a} = Σ_{o ↦ x} c.bobAccEffect κ o a` (Eqs. (17), (18)).
The averaged identities are written with the conditioning multiplied out:
`E[r_j(T) m_j] = Σ_o Σ_z Re Tr(ζ̃_{x,z} σ_j) · Re Tr(td_o M_j)` and
`E[m_j²] = Σ_o Σ_z Re Tr(ζ̃_{x,z}) · Re Tr(td_o M_j²)`, `x = o.take (lx κ)`. -/
theorem lemma_13_sender_moments (c : Certificate) (κ : ℕ) (hA : 1 ≤ (c.A κ).nq) :
    (∀ (x : Str) (z : Bits (c.A κ).width), 0 < c.prepProb κ x z →
      let r : EuclideanSpace ℝ (Fin 3) :=
        ((c.prepared κ x z).trace.re)⁻¹ • blochVec (c.prepared κ x z)
      let a : Str := (c.A κ).clOut z
      let w : EuclideanSpace ℝ (Fin 3) :=
        (2 * c.questionProb κ x)⁻¹ •
          ∑ o : Bits (c.Qg κ).outC.length,
            if (List.ofFn o).take (c.lx κ) = x then blochVec (c.bobAccEffect κ (List.ofFn o) a)
            else 0
      (1 / 3) * ∑ j : Fin 3, r j * c.senderMoment κ x a j 1 = (2 / 3) * inner ℝ r w ∧
        (1 / 3) * ∑ j : Fin 3, c.senderMoment κ x a j 2 ≤ 1 / 3) ∧
    (1 / 3) * ∑ j : Fin 3, ∑ o : Bits (c.Qg κ).outC.length, ∑ z : Bits (c.A κ).width,
        (c.prepared κ ((List.ofFn o).take (c.lx κ)) z * pauli j).trace.re *
          (c.td κ (List.ofFn o) * c.senderObs κ (List.ofFn o) ((c.A κ).clOut z) j).trace.re =
      2 * c.align κ / 3 ∧
    (1 / 3) * ∑ j : Fin 3, ∑ o : Bits (c.Qg κ).outC.length, ∑ z : Bits (c.A κ).width,
        (c.prepared κ ((List.ofFn o).take (c.lx κ)) z).trace.re *
          (c.td κ (List.ofFn o) * (c.senderObs κ (List.ofFn o) ((c.A κ).clOut z) j) ^ 2).trace.re ≤
      1 / 3 := by sorry

end CompNonlocal
