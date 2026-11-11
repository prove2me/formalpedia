-- Prove2me | Theorems.Thm_DepthOptQC_Synth_eq_61
-- name    : DepthOptQC.Synth.eq_61
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:57.707901+00:00
-- url     : https://prove2.me/theorems/1077a455-a2bb-40df-9018-509d0cb73deb
-- title:
--   Eq. (61) — the cubic block identity $\mathcal B(\mathrm{Amp}(W))=-3\mathcal B+4\mathcal B\mathcal B^\dagger\mathcal B$
-- statement:
--   Let $A$ be an ancilla register with all-zero state $|0\rangle_A$, $S$ a system register, $V_0=|0\rangle_A\otimes I_S$, $\Pi=V_0V_0^\dagger$ and $R_\Pi=I-2\Pi$. For every unitary $W$ on $A\otimes S$, with distinguished block $\mathcal B=\mathcal B(W)=V_0^\dagger WV_0$ and $\mathrm{Amp}(W)=WR_\Pi W^\dagger R_\Pi W$,
--   $$
--   \mathcal B\big(\mathrm{Amp}(W)\big) = -3\,\mathcal B + 4\,\mathcal B\mathcal B^\dagger\mathcal B .
--   $$
--
--   In particular, if $\mathcal B=U/2$ with $U$ unitary then the amplified block is $-U$. The identity is the exact input to the robust amplification bound (Lemma 5).
--
--   **Formalization Note** The ancilla register is any finite type $A$ with a distinguished point $a_0$ and the system any finite type.
--
--   Differences from the source:
--   - generalization: A an a-qubit ancilla register with zero state 0^a, S the system register → any finite type A with a point a₀, any finite system type Sy; reason: the identity is algebraic; the paper's registers are the instance A = {0,1}^a, a₀ = 0^a
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §3.3.1, Eqs. (60)–(61), p.21

import Definitions.Def_DepthOptQC_Synth_amp

namespace DepthOptQC.Synth

/-- **Eq. (61): the cubic block identity of one amplification step** (Vasconcelos, *Depth-Optimal
Quantum Compilation*, arXiv:2609.34659, §3.3.1, Eqs. (60)–(61), p.21). For a unitary `W`, with
distinguished block `B := V₀† W V₀` and `Amp(W) := W R_Π W† R_Π W`,
`B(Amp(W)) = −3B + 4BB†B`.

**Formalization Note.** The ancilla register is any finite type `A` with zero point `a₀` and the
system any finite type `Sy` (the paper: an `a`-qubit register and a system register); the identity
uses `W†W = I`, so `W` is assumed unitary as in the paper. -/
theorem eq_61 {A Sy : Type*} [Fintype A] [DecidableEq A] [Fintype Sy] [DecidableEq Sy] (a₀ : A)
    (W : Matrix (A × Sy) (A × Sy) ℂ) (hW : W ∈ Matrix.unitaryGroup (A × Sy) ℂ) :
    block a₀ (amp a₀ W) = (-3 : ℂ) • block a₀ W +
      (4 : ℂ) • (block a₀ W * (block a₀ W).conjTranspose * block a₀ W) := by sorry

end DepthOptQC.Synth
