-- Prove2me | Theorems.Thm_CodedSorting_lemma_5_2_5_3
-- name    : CodedSorting.lemma_5_2_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:57.384839+00:00
-- url     : https://prove2.me/theorems/12503474-ec70-4d79-88f9-4e8be3688874
-- title:
--   Lemmas 5.2–5.3 — the global circuit: $W=24{,}432{,}543$ inputs, $S=12{,}508{,}242{,}237<Wm$, full-rank sessions
-- statement:
--   Let $v=111$, $R=439$, $c=63$ and $m=8^3=512$. Suppose a local circuit with the properties of Lemma 5.1 exists. Then there is a binary linear circuit on the
--   $$W=6v^3+3v^2R=24{,}432{,}543$$
--   global registers (three data grids of $v^3$ pairs $X_a,Y_a$ and $3v^2$ shared pools of $R$ auxiliary registers) with admissible subspace labels in $H=\mathbb Q^{512}$ such that
--
--   1. it exchanges the initial values of $X_a$ and $Y_a$ in each of the three data copies and restores every auxiliary initial value (Lemma 5.2); temporary wires are not registers, so they add no inputs or sessions;
--   2. the ranks of the $W$ source–sink projection differences sum to $Wm=3v^2(2v+R)m=12{,}509{,}462{,}016$;
--   3. the total edge length is
--   $$S=6v^3(m-1)+3v^2Rm+9v^2c=Wm-3v^2(2v-3c)=12{,}508{,}242{,}237<Wm;\tag{8}$$
--   4. every session $s_i\to t_{\sigma(i)}$ has $U_{t_{\sigma(i)}}=U_{s_i}^\perp$, $\dim(U_{s_i}+U_{t_{\sigma(i)}})=m$ and
--   $$\operatorname{rank}_{\mathbb Q}\big(M_{t_{\sigma(i)}}-M_{s_i}\big)=m,\tag{9}$$
--   where $M$ is the orthogonal projection onto the label.
--
--   These lemmas give the inequality $S<Wm$ on which both the coding counterexample and the external-memory recursion rest: each data pair saves two units of length while the temporary wires cost on average $3\cdot63/111<2$.
--
--   **Formalization Note** The construction of §5.1 (three tensor rounds of local invocations, reverse invocations, shared pools) is given in prose only; the lemmas are therefore stated as an implication from the local circuit to a global circuit with every stated property. The numeric identities of (8) are kept as stated.
--
--   Differences from the source:
--   - reading: "the operation sequence" and "the full circuit": the three-round construction of §5.1 applied to the circuit of Lemma 5.1 → if a local circuit with the properties of Lemma 5.1 exists, then some labeled circuit on the $W$ global registers has every property the two lemmas state; reason: the construction is specified in prose only; every clause of both lemmas is kept
--   - generalization: the sink/source dimension and rank conditions (9) → also $U_{t_{\sigma(i)}}=U_{s_i}^\perp$ for every session; reason: shown in the proof of Lemma 5.3 and used in Lemma 6.2 (p.23); dropping the clause gives the printed statement
--   - encoding: $H=E_1\otimes E_2\otimes E_3$ with the tensor inner product → $\mathbb Q^{512}$ (`Fin 512 → ℚ`) with the coordinate dot product; reason: an orthonormal basis identifies them
--   - encoding: $M_u=P_{U_u}$, the orthogonal projection → every matrix $P$ with `IsOrthProj U P`; reason: over $\mathbb Q$ it exists and is unique
--   - encoding: "Temporary wires introduce no independent inputs or additional sessions" → temporary wires are not registers of the circuit type; reason: inputs and sessions are indexed by registers
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 5.2, p.15 (PDF 16), and Lemma 5.3, p.16 (PDF 17)

import Mathlib
import Definitions.Def_CodedSorting_LocalCircuit
import Definitions.Def_CodedSorting_Sessions

namespace CodedSorting

/-- **Lemmas 5.2 and 5.3 (Permutation of the input bits; total edge length and ranks of
source–sink matrix differences)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), pp.15–16.

From a local circuit with the properties of Lemma 5.1 one obtains a global labeled circuit (three
data grids of `v³` pairs `(X_a, Y_a)` and `3v²` shared pools of `R` auxiliary registers, labels in
`H = ℚ⁵¹²`) such that:
1. it exchanges the initial values of `X_a, Y_a` in each of the three copies and restores every
   auxiliary value (Lemma 5.2);
2. it has `W = 6v³ + 3v²R = 24,432,543` inputs; temporary wires are not registers, so they
   introduce no inputs or sessions (Lemma 5.2);
3. the ranks of the `W` source–sink projection differences sum to `Wm = 3v²(2v + R)m =
   12,509,462,016` (Lemma 5.3);
4. the total edge length is `S = 6v³(m − 1) + 3v²Rm + 9v²c = Wm − 3v²(2v − 3c) = 12,508,242,237 < Wm`,
   (8);
5. for every session `s_i → t_{σ(i)}`, `U_t = U_s^⊥`, `dim(U_{s_i} + U_{t_{σ(i)}}) = m = 512` and
   `rank_ℚ(M_{t_{σ(i)}} − M_{s_i}) = m`, (9).

**Formalization Note.** The paper proves these lemmas for its three-round construction (§5.1),
which is described in prose only; here they are stated as: every local circuit with Lemma 5.1's
properties yields a global labeled circuit with every property the two lemmas state. The number of
temporary wires is left free. `U_t = U_s^⊥` is shown in the proof of Lemma 5.3 and used in
Lemma 6.2 (p.23). The numeric identities of (8) are kept as stated. -/
theorem lemma_5_2_5_3 :
    (∃ (ℓ : Fin 111 → Submodule ℚ (Fin 8 → ℚ)) (π : Equiv.Perm (Fin 111))
      (C : XorCircuit LocalReg (Fin 9)) (lab : Node LocalReg C.G → Submodule ℚ (Fin 8 → ℚ)),
      IsLocalCircuit ℓ π C lab) →
    ∃ (n : ℕ) (C : XorCircuit GlobalReg (Fin n))
      (lab : Node GlobalReg C.G → Submodule ℚ (Fin 512 → ℚ)),
      C.Implements (fun x i => x (globalSwap i)) ∧
      LabeledCircuit C lab ∧
      Fintype.card GlobalReg = 24432543 ∧
      6 * 111 ^ 3 + 3 * 111 ^ 2 * 439 = 24432543 ∧
      SessionLabels C globalSwap lab ∧
      (∀ P Q : GlobalReg → Matrix (Fin 512) (Fin 512) ℚ,
        (∀ i, IsOrthProj (lab (.source i)) (P i)) →
        (∀ i, IsOrthProj (lab (.sink (globalSwap i))) (Q i)) →
        ∑ i, (Q i - P i).rank = 12509462016) ∧
      3 * 111 ^ 2 * (2 * 111 + 439) * 512 = 12509462016 ∧
      totalLength C lab = 12508242237 ∧
      6 * 111 ^ 3 * (512 - 1) + 3 * 111 ^ 2 * 439 * 512 + 9 * 111 ^ 2 * 63 = 12508242237 ∧
      12509462016 - 3 * 111 ^ 2 * (2 * 111 - 3 * 63) = 12508242237 ∧
      12508242237 < 12509462016 := by sorry

end CodedSorting
