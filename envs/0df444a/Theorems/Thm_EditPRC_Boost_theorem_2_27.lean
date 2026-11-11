-- Prove2me | Theorems.Thm_EditPRC_Boost_theorem_2_27
-- name    : EditPRC.Boost.theorem_2_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:09:24.403635+00:00
-- url     : https://prove2.me/theorems/f5d650ba-5a54-4c0c-af32-aa4a76bf07de
-- title:
--   Theorem 2.27 — sub-exponentially secure PRCs give sub-exponentially secure PRFs running in time $O(n^{1+\theta})$ for every $\theta>0$
-- statement:
--   Suppose there is a sub-exponentially secure pseudorandom code: finite alphabets $M,S$ and a PRC $P$ with message alphabet $M$ and codeword alphabet $S$ (Definition 2.1) such that
--   1. KeyGen, Enc and Dec are polynomial-time algorithms and the blocklength is $n(\lambda)=\lambda$;
--   2. for some constant $c>0$, every distinguisher running in time $2^{O(\lambda^c)}$ has advantage $2^{-\omega(\lambda^c)}$ against the oracle $\mathrm{Enc}_{\mathrm{sk}}(\cdot)$ versus the uniformly random oracle;
--   3. $P$ is sound (negligible failure) and correct: $\Pr[\mathrm{Dec}_{\mathrm{sk}}(\mathrm{Enc}_{\mathrm{sk}}(m))=m]\ge1-\mathrm{negl}(\lambda)$ for every $m$.
--
--   Then for every constant $\theta>0$ there is a well-formed keyed family $\mathrm{PRF}:\{0,1\}^{\kappa(n)}\times\{0,1\}^n\to\{0,1\}^{m(n)}$ that is sub-exponentially secure and runs in time $O(n^{1+\theta})$:
--   $$\forall\theta>0\ \ \exists\,\mathrm{PRF}:\quad \text{advantage } 2^{-\omega(n^{c'})}\ \text{against time } 2^{O(n^{c'})}\ (\text{some } c'>0),\qquad \mathrm{time}(\mathrm{PRF})=O(n^{1+\theta}).$$
--
--   In the paper this is the route PRC $\Rightarrow$ OWF $\Rightarrow$ PRG $\Rightarrow$ PRF with sub-exponential security preserved, followed by an input-shrinking step for speed. The boost of Theorem 3.12 uses such PRFs as one-time pads and as seeds for synchronization strings.
--
--   Differences from the source:
--   - reading: "sub-exponentially secure PRCs" → a PRC of Definition 2.1 with polynomial-time algorithms and blocklength $n(\lambda)=\lambda$ (the paper's convention, p. 10) whose pseudorandomness holds against every distinguisher running in time $2^{C\lambda^c}$ with advantage at most $2^{-K\lambda^c}$ eventually for every $K$, for some $c>0$; reason: the notation of p. 8 with $s(\lambda)=n^c$.
--   - generalization: the notation of p. 8 sets every $\mathrm{negl}$ to $2^{-\omega(s)}$ → soundness and correctness errors of the assumed PRC are only required to be negligible; reason: a weaker hypothesis; a PRC with $2^{-\omega(s)}$ errors satisfies it, so the statement specializes to the source's.
--   - generalization: "PRCs" (robust to some ball $B(x,*)$ centered at $x$) → robustness only to the trivial ball $B_E(x,0)=\{x\}$, i.e. correctness, and any message alphabet and message length; reason: every ball of Definition 2.1 contains its center, so every PRC of the paper satisfies this weaker hypothesis.
--   - reading: "running time $O(n^{1+\theta})$" → one Turing machine (Mathlib `TM2`) computes $\mathrm{PRF}(k,x)$ from the encoding of $(1^n,k,x)$ within $Cn^{1+\theta}+C$ steps; reason: the machine model is unspecified; the additive constant is the usual meaning of $O(\cdot)$ at small $n$.
--   - reading: "for any constant $\theta>0$" → for every $\theta>0$ there is a family (it may depend on $\theta$); reason: the order of quantifiers in the sentence and in §2.6.
--   - encoding: $m=\mathrm{poly}(n)$ → $\kappa$ and $m$ polynomially bounded and $m(n)\ge1$; reason: keys are sampled efficiently; $m\ge1$ only excludes the empty-output family, which is not a PRF.
--   - encoding: machines → multi-stack Turing machines on bit encodings, randomized algorithms read their coins as input, distinguishers are oracle algorithms whose time is counted as in `EditPRC.Boost.Machine`; reason: Lean convention.
--
--   **Formalization Note.** The sub-exponential exponent $c'$ of the PRF is existentially quantified inside `PRF.SubexpSecure`, independently of the PRC's $c$, as in the theorem's wording.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 18, Theorem 2.27 (notation p. 8)

import Mathlib
import Definitions.Def_EditPRC_Boost_PRC
import Definitions.Def_EditPRC_Boost_PRF

namespace EditPRC.Boost

/-- **Theorem 2.27.** If a sub-exponentially secure PRC exists, then for every constant `θ > 0`
there is a sub-exponentially secure PRF whose evaluation runs in time `O(n^{1+θ})`. -/
theorem theorem_2_27
    (hP : ∃ (M S : Type) (_ : Fintype M) (_ : Fintype S) (_ : Nonempty M) (P : PRC M S)
      (c : ℝ), 0 < c ∧ P.Efficient ∧ P.SubexpPseudorandom c ∧ P.Sound ∧ P.EditRobust 0 ∧
      ∀ lam, P.blockLen lam = lam) :
    ∀ θ : ℝ, 0 < θ → ∃ F : PRF, F.WellFormed ∧ F.SubexpSecure ∧ F.RunsInTime θ := by sorry

end EditPRC.Boost
