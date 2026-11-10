-- Prove2me | Theorems.Thm_DQILocal_Recon_proposition_4_3
-- name    : DQILocal.Recon.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:03.103683+00:00
-- url     : https://prove2.me/theorems/d3b9cb1b-9f33-42ca-8306-c78cc183af1d
-- title:
--   Proposition 4.3 — optimal tree decoding: the optimum over all measurements is $P_t$, attained by depth-$t$ BPQM
-- statement:
--   Let $q\ge2$, $f$ any cost, $\beta\ge0$, $k\ge2$, $D\ge2$, and $p=p_\beta$. Draw $y$ uniformly from the tree code $C_t$ and give a decoder the state $\bigotimes_{v\in\mathcal T_t}|\psi^p_{y_v}\rangle$. Then:
--
--   1. the largest probability, over all measurements, of outputting the root value $y_{\mathrm{root}}$ equals $P_t=\mathbb E\,S(N^{(t)})$;
--   2. depth-$t$ BPQM over $\mathbb Z_q$ is a measurement that attains it, for every choice of the symbol-node unitaries;
--   3. $P_t\le P_{t+1}\le1$;
--   4. for every probability vector $\nu$, $S(\nu)=1$ if and only if $\nu=\mathrm u$.
--
--   The optimum over measurements, the recursion value $P_t$ and the BPQM success probability are three independently defined numbers; the proposition identifies them.
--
--   Differences from the source:
--   - encoding: a measurement (possibly with ancillas and work registers) → a POVM on the system (positive semidefinite elements summing to the identity); reason: Naimark dilation: the two describe the same outcome laws
--   - reading: depth-t BPQM over ℤ_q (symbol-node unitary fixed only by its mapping property; order of combining children unspecified) → every BPQMChoice U, children combined in index order; reason: the paper does not fix these choices; quantifying over all of them is the stronger reading
--   - reading: BPQM "attains" the optimum → bpqm is a POVM and its root success equals P_t; reason: attaining the optimum over measurements presupposes that BPQM is a measurement
--   - encoding: the tree T_t and its vertices → index paths (List ℕ): root [], child checks v ++ [a], child symbols c ++ [b]; reason: a labelling of the same tree
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Proposition 4.3, p. 24

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_TreeCode
import Definitions.Def_DQILocal_Recon_BPQM

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder

/-- **Proposition 4.3 (Optimal tree decoding).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Proposition 4.3, p. 24.
"Draw `y` uniformly from `C_t` and give a decoder the state `⊗_{v∈T_t} |ψ^p_{y_v}⟩`. The largest
probability, over all measurements, of outputting the root value `y_root` is `P_t`, and depth-`t`
BPQM over `ℤ_q`, described in Section 3.3, attains it. Moreover `P_t ≤ P_{t+1} ≤ 1`, and
`S(ν) = 1` if and only if `ν = u`."

Standing assumptions (§3.1, p. 15): `q ≥ 2`, any cost `f`, `β ≥ 0`, `k ≥ 2`, `D ≥ 2`;
`p = p_β` is the Gibbs weight.

**Formalization Note.** "Over all measurements" is `treeOpt`, the supremum over every POVM on the
qudits of `T_t` (ancillas absorbed by Naimark). BPQM is the POVM `bpqm`, for **every** choice `U`
of the symbol-node unitaries (the paper fixes them only up to the property of Lemma 4.1(1)); that
it is a measurement is part of "attains it". `P_t` is Definition 4.2's expectation, defined
independently of both. -/
theorem proposition_4_3 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (k D : ℕ) (hk : 2 ≤ k) (hD : 2 ≤ D) (t : ℕ) :
    treeOpt q k D t (gibbsWeight q f β) = Pt k D q f β t ∧
    (∀ U : BPQMChoice q, IsPOVM (bpqm k D t (gibbsWeight q f β) U) ∧
      treeSuccess k D t (gibbsWeight q f β) (bpqm k D t (gibbsWeight q f β) U) = Pt k D q f β t) ∧
    Pt k D q f β t ≤ Pt k D q f β (t + 1) ∧ Pt k D q f β (t + 1) ≤ 1 ∧
    ∀ ν : ZMod q → ℝ, IsProbVec ν → (succFn ν = 1 ↔ ν = unif q) := by sorry

end DQILocal.Recon
