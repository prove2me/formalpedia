-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_7_2
-- name    : BlockOrthoCSP.Decide.lemma_F_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:15:13.466217+00:00
-- url     : https://prove2.me/theorems/ff7cabaf-03ad-4001-8b3a-bc7d005d8064
-- title:
--   Lemma F.7.2 — a relation with an equality-free pp-definition over generated supports is a generated support, and a realizing instance is computable
-- statement:
--   Let $q\ge 1$, $\mathcal F$ a finite set of algebraic-valued constraint functions, $h \ge 1$ and $F_1,\dots,F_h \in W_{\mathcal F}$. Let $x = (x_1,\dots,x_\ell)$, $\ell \ge 1$, be free variables and $y = (y_1,\dots,y_s)$, $s \ge 0$, existential ones; let $E$ be a finite set of atoms, each with $i(e) \in [h]$ and an ordered scope $z_e$ of length $\operatorname{arity}(F_{i(e)})$ over $x$ and $y$ (repetitions allowed). Define $R \subseteq D^\ell$ by
--   $$R(x) \iff \exists y \bigwedge_{e\in E} \Phi_{F_{i(e)}}(z_e).$$
--   Then some $H \in W_{\mathcal F}$ has $\Phi_H = R$. Moreover, given instances $I_i$ with $F_i = F_{I_i}^{[r_i]}$, $r_i = \operatorname{arity}(F_i)$, an instance $J$ with $\Phi_{F_J^{[\ell]}} = R$ is computed by a terminating exact search: one computable function of the codes of the input, the instances and the formula.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - encoding: exact input (q, F): 'standard exact representations specifying the chosen complex root' [Coh93] → LangCode = (q, list of (r, list of q^r AlgCode values in lexicographic order of D^r)); an AlgCode is a nonzero integer polynomial with a closed rational box isolating exactly one root (LangCode.Valid); decodeLang identifies duplicate functions; reason: one standard exact representation; every algebraic number has such a code, so every admissible (q, F) is decoded from a valid code; invalid codes may get any answer
--   - encoding: E a finite set indexing the atoms; i(e) ∈ [h]; scopes z_e over x and y → atoms indexed by Fin nE, idx : Fin nE → Fin h, scope e : Fin (arity F_{i(e)}) → Fin (ℓ + s) (the first ℓ variables are x); the algorithm receives them as ppCode (index, variable numbers); reason: every finite index set can be enumerated; variable numbering is a renaming
--   - encoding: instances I_i with F_i = F_{I_i}^{[r_i]} → instance codes cI i that decode (with r_i retained variables) to Is i with (Is i).genFn = F_i; reason: the instance is given by its code
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-30, Lemma F.7.2

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Codes
import Definitions.Def_BlockOrthoCSP_Decide_Realization

namespace BlockOrthoCSP.Decide

/-- Lemma F.7.2, p. F-30: an equality-free pp-formula over generated supports defines a generated
support; and, given representing instances `I_i` (with `F_i = F_{I_i}^{[r_i]}`), an instance
realizing it is computable. -/
theorem lemma_F_7_2 :
    (∀ (q : ℕ), 1 ≤ q → ∀ F : Finset (CFn q), IsAlgLanguage F →
      ∀ (h ℓ s nE : ℕ) (Fs : Fin h → CFn q) (idx : Fin nE → Fin h)
        (scope : (e : Fin nE) → Fin (Fs (idx e)).1 → Fin (ℓ + s)),
        1 ≤ h → 1 ≤ ℓ → (∀ i, Fs i ∈ W F) →
          ∃ H : (Fin ℓ → Fin q) → ℂ, (⟨ℓ, H⟩ : CFn q) ∈ W F ∧ Phi H = ppRel Fs idx scope) ∧
    ∃ alg : LangCode × List (ℕ × InstCode) × (ℕ × ℕ × List (ℕ × List ℕ)) → InstCode,
      Computable alg ∧
      ∀ c : LangCode, c.Valid →
        ∀ (h ℓ s nE : ℕ) (Fs : Fin h → CFn c.1) (idx : Fin nE → Fin h)
          (scope : (e : Fin nE) → Fin (Fs (idx e)).1 → Fin (ℓ + s))
          (cI : Fin h → InstCode) (Is : (i : Fin h) → Inst c.1 (Fs i).1),
          1 ≤ h → 1 ≤ ℓ → (∀ i, Fs i ∈ W (decodeLang c)) →
          (∀ i, decodeInst c (Fs i).1 (cI i) = some (Is i) ∧ (Is i).genFn = (Fs i).2) →
            ∃ J : Inst c.1 ℓ,
              decodeInst c ℓ
                  (alg (c, List.ofFn (fun i => ((Fs i).1, cI i)), (ℓ, s, ppCode Fs idx scope))) =
                some J ∧
              Phi J.genFn = ppRel Fs idx scope := by sorry

end BlockOrthoCSP.Decide
