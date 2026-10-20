-- Prove2me | solution 1 for mme_complex_arithmetic_omega_le_matMulExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T19:37:23.688967+00:00
-- url     : https://prove2.me/submissions/735d10d5-2bcc-4af0-8860-afcdac3ad5ee

/-
Port of OpenAI math, source revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This proof uses the original arithmetic model, imported from its definition item.

OAI-Lean-Apache-2.0.txt
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.


FixedPointTheorems-MIT.txt
Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-/

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_mme_omega

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/
private theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t e : α} : ite c t e = t := if_pos hc
private theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t e : α} : ite c t e = e := if_neg hnc
private theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := dif_pos hc
private theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc := dif_neg hnc
/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/
private theorem toAntisymmetrization_eq {α : Type u} (r : α → α → Prop)
    [IsPreorder α r] (a b : α) :
    toAntisymmetrization r a = toAntisymmetrization r b ↔ AntisymmRel r a b :=
  Quotient.eq

end CompatibilityAliases


/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor -/
section FlattenModule000






namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

section ComplexTopology

variable {X Y Z X' Y' Z' : Type*}

def BorderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) : Prop :=
  T ∈ closure {S | RankAtMost S r}

def restrictionOrbit [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Set (Tensor ℂ X' Y' Z') :=
  {U | ∃ (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    U = restrict A B C T}

def DegeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  U ∈ closure (restrictionOrbit T)

theorem RankAtMost.borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : RankAtMost T r) :
    BorderRankAtMost T r := subset_closure h

theorem continuous_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Continuous (Tensor.restrict A B C) := by
  unfold restrict
  fun_prop

theorem BorderRankAtMost.restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : BorderRankAtMost T r)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    BorderRankAtMost (Tensor.restrict A B C T) r := by
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.restrict A B C S) r} :=
    isClosed_closure.preimage (continuous_restrict A B C)
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.restrict A B C S) r} := by
    intro S hS
    exact (hS.restrict A B C).borderRankAtMost
  exact closure_minimal hsubset hclosed h

theorem continuous_product_left {U V W : Type*} (S : Tensor ℂ U V W) :
    Continuous (fun T : Tensor ℂ X Y Z => Tensor.product T S) := by
  unfold product
  fun_prop

theorem continuous_product_right {U V W : Type*} (T : Tensor ℂ X Y Z) :
    Continuous (fun S : Tensor ℂ U V W => Tensor.product T S) := by
  unfold product
  fun_prop

theorem BorderRankAtMost.product {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W} {r s : ℕ}
    (hT : BorderRankAtMost T r) (hS : BorderRankAtMost S s) :
    BorderRankAtMost (Tensor.product T S) (r * s) := by
  have hexact : ∀ T' : Tensor ℂ X Y Z, RankAtMost T' r →
      BorderRankAtMost (Tensor.product T' S) (r * s) := by
    intro T' hT'
    have hclosed : IsClosed {S' : Tensor ℂ U V W |
        BorderRankAtMost (Tensor.product T' S') (r * s)} :=
      isClosed_closure.preimage (continuous_product_right T')
    have hsubset : {S' : Tensor ℂ U V W | RankAtMost S' s} ⊆
        {S' | BorderRankAtMost (Tensor.product T' S') (r * s)} := by
      intro S' hS'
      exact (hT'.product hS').borderRankAtMost
    exact closure_minimal hsubset hclosed hS
  have hclosed : IsClosed {T' : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.product T' S) (r * s)} :=
    isClosed_closure.preimage (continuous_product_left S)
  exact closure_minimal hexact hclosed hT

theorem BorderRankAtMost.of_degeneration [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {r : ℕ}
    (hT : BorderRankAtMost T r) (hTU : DegeneratesTo T U) :
    BorderRankAtMost U r := by
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | BorderRankAtMost S r} := by
    rintro S ⟨A, B, C, rfl⟩
    exact hT.restrict A B C
  exact closure_minimal hsubset isClosed_closure hTU

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule000
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity -/
section FlattenModule001



namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

def eval {n : ℕ} (P : MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, P.eval A B = A * B

def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

theorem correct_iff_entries {n : ℕ} (P : MatrixAlgorithm n) :
    P.Correct ↔ ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct : scalarAlgorithm.Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

noncomputable def omega : ℝ := sInf {τ : ℝ | AdmissibleExponent τ}

end Arithmetic

namespace Tensor

def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule001
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching -/
section FlattenModule002

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule002
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor -/
section FlattenModule003




namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication a b c = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_product_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r s : ℕ}
    (hT : RankAtMost (matrixCoefficients (K := K) A B C) r)
    (hS : RankAtMost (matrixCoefficients (K := K) D E F) s) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) (r * s) :=
  matrixCoefficients_rank_of_product (hT.product hS)

theorem matrixCoefficients_batch_rank [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r batches : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hfit : R ≤ batches * k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B)) (batches * r) :=
  matrixCoefficients_rank_of_product (houter.batch_product hbatch hfit)

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

theorem matrixCoefficients_cyclic_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {r : ℕ} (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) B C A) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  rw [← matrixCoefficients_cyclic (K := K) x y z]
  rw [congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule003
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening -/
section FlattenModule004


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule004
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent -/
section FlattenModule005


namespace OAI

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → ℂ := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → ℂ := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → ℂ := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite complex coefficient tensor. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (A : X' → X → ℂ) (B : Y' → Y → ℂ)
    (C : Z' → Z → ℂ) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (n : ℕ) : ℕ := exactRank (Tensor.matrixMultiplication n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication n n n) (exactMatrixRank n) :=
  exactRank_spec _

/-- The ordinary scalar multiplication algorithm uses `n³` simple tensors. -/
theorem matrixMultiplication_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication n n n) (n ^ 3) := by
  classical
  let a : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p x => if x = (p.1, p.2.1) then 1 else 0
  let b : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p y => if y = (p.2.1, p.2.2) then 1 else 0
  let c : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p z => if z = (p.2.2, p.1) then 1 else 0
  have heq : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Tensor.matrixMultiplication,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite]
    split_ifs <;> simp_all
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne a b c using 1
  simp [Fintype.card_prod, pow_succ, Nat.mul_assoc]

theorem exactMatrixRank_upper (n : ℕ) : exactMatrixRank n ≤ n ^ 3 :=
  exactRank_le (matrixMultiplication_rankAtMost_cubic n)

/-- An identity minor of the output flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have hminor : ∀ i k : Fin n × Fin n,
      Tensor.matrixMultiplication n n n (i.2, j) (j, i.1) k =
        if i = k then 1 else 0 := by
    intro i k
    simp [Tensor.matrixMultiplication, Prod.ext_iff, eq_comm]
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j))
    (fun i : Fin n × Fin n => (j, i.1)) id hminor
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank n :=
  matrixMultiplication_rank_lower hn (exactMatrixRank_spec n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < exactMatrixRank n :=
  lt_of_lt_of_le (pow_pos hn 2) (exactMatrixRank_lower hn)

@[simp] theorem exactMatrixRank_zero : exactMatrixRank 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using exactMatrixRank_upper 0)

@[simp] theorem exactMatrixRank_one : exactMatrixRank 1 = 1 := by
  apply le_antisymm
  · simpa using exactMatrixRank_upper 1
  · simpa using exactMatrixRank_lower (n := 1) zero_lt_one

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent : ℝ := sInf exactRankExponentSet

theorem exactRankExponentSet_nonempty : exactRankExponentSet.Nonempty :=
  ⟨Real.logb 2 (exactMatrixRank 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactMatrixRank_logb_upper {n : ℕ} (hn : 2 ≤ n) :
    Real.logb n (exactMatrixRank n) ≤ 3 := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.logb_le_iff_le_rpow hn1 hr).mpr
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast exactMatrixRank_upper n

theorem exactRankExponentSet_bddBelow : BddBelow exactRankExponentSet := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact exactMatrixRank_logb_lower hn

theorem exactRankExponent_lower : 2 ≤ exactRankExponent :=
  le_csInf exactRankExponentSet_nonempty (by
    rintro τ ⟨n, hn, rfl⟩
    exact exactMatrixRank_logb_lower hn)

theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    exactRankExponent ≤ Real.logb n (exactMatrixRank n) :=
  csInf_le exactRankExponentSet_bddBelow ⟨n, hn, rfl⟩

theorem exactRankExponent_upper : exactRankExponent ≤ 3 :=
  (exactRankExponent_le_logb (n := 2) le_rfl).trans
    (exactMatrixRank_logb_upper (n := 2) le_rfl)

/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp (exactRankExponent_le_logb hn)

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  by_cases hn2 : 2 ≤ n
  · exact exactMatrixRank_rpow_lower hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ

/-- Finite decompositions approximate the exact-rank exponent with any positive slack. -/
theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ (exactRankExponent + ε) := by
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right _ hε)
  exact ⟨n, exactMatrixRank n, hn, exactMatrixRank_spec n, hR.le⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule005
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs -/
section FlattenModule006


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate Input R → Gate Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate Input R) (f : R → S)
    (inputs : Input → ℂ) (registers : S → ℂ) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

@[simp] theorem cost_mapRegister (g : Gate Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program Input r) : {s : ℕ} → Program Input s → Program Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

@[simp] theorem cost_append {r s : ℕ} (p : Program Input r) (q : Program Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (Input : Type*) where
  | constant : ℂ → Expression Input
  | input : Input → Expression Input
  | add : Expression Input → Expression Input → Expression Input
  | sub : Expression Input → Expression Input → Expression Input
  | mul : Expression Input → Expression Input → Expression Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → ℂ) : Expression Input → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule006
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition -/
section FlattenModule007

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ ℂ) : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r)
    (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ ℂ) : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program Input r) (q : Program Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program Input r} {q : Program Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate Mid (Fin s)) (h : Gate Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program Input r) :
    {s : ℕ} → (q : Program Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule007
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.MatrixPadding -/
section FlattenModule008

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

def zeroPadMatrix {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {n m : ℕ} (h : n ≤ m)
    (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    (zeroPadMatrix m A * zeroPadMatrix m B) (Fin.castLE h i) (Fin.castLE h k) =
      (A * B) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin m,
        zeroPadMatrix m A (Fin.castLE h i) j *
          zeroPadMatrix m B j (Fin.castLE h k)) =
        ∑ j : Fin n,
          zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) *
            zeroPadMatrix m B (Fin.castLE h j) (Fin.castLE h k) := by
      apply sum_fin_castLE_of_zero h
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin n, A i j * B j k := by simp

def padSource {n m : ℕ} : MatrixInput m → MatrixInput n ⊕ ℂ
  | .inl (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inr (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {n m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fun x : MatrixInput m => Sum.elim (matrixInputs A B) id (padSource x)) =
      matrixInputs (zeroPadMatrix m A) (zeroPadMatrix m B) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨i, j⟩
  all_goals
    by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]

namespace MatrixAlgorithm

def pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) : MatrixAlgorithm n where
  registers := P.registers
  program := P.program.mapSource (padSource (n := n))
  output := fun i k => P.output (Fin.castLE h i) (Fin.castLE h k)

theorem pad_correct {n m : ℕ} (h : n ≤ m) {P : MatrixAlgorithm m}
    (hP : P.Correct) : (pad h P).Correct := by
  intro A B
  funext i k
  change (P.program.mapSource (padSource (n := n))).eval (matrixInputs A B)
    (P.output (Fin.castLE h i) (Fin.castLE h k)) = (A * B) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix m A) (zeroPadMatrix m B)) (Fin.castLE h i)) (Fin.castLE h k)
  exact hentry.trans (zeroPadMatrix_mul h A B i k)

@[simp] theorem pad_cost_eq {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) :
    (pad h P).cost = P.cost :=
  Program.cost_mapSource (padSource (n := n)) P.program

theorem exists_restrict {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m)
    (hP : P.Correct) : ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad h P, pad_correct h hP, (pad_cost_eq h P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule008
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.MatrixPadding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily -/
section FlattenModule009



namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.Expression

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Foundation.Arithmetic.Expression

end

end OAI

end FlattenModule009
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.RecursiveBlockPrograms -/
section FlattenModule010





namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

namespace LinearExpression

variable {Input : Type*}

def sumFin : (n : ℕ) → (Fin n → Expression Input) → Expression Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin n (fun i => f i.succ))

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

def linear {Term : Type*} [Fintype Term] (a : Term → ℂ) (wire : Term → Input) :
    Expression Input :=
  sumFin (Fintype.card Term) (fun i =>
    .mul (.constant (a ((Fintype.equivFin Term).symm i)))
      (.input (wire ((Fintype.equivFin Term).symm i))))

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) (inputs : Input → ℂ) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

structure Family (Input Output : Type*) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family Input Output) (inputs : Input → ℂ) (o : Output) : ℂ :=
  p.program.eval inputs (p.output o)

def cost (p : Family Input Output) : ℕ := p.program.cost

def expressions [Fintype Output] (e : Output → Expression Input) : Family Input Output :=
  let p := Expression.compileFamily e
  ⟨p.registers, p.program, p.output⟩

theorem eval_expressions [Fintype Output] (e : Output → Expression Input)
    (inputs : Input → ℂ) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

def compose (p : Family Input Mid) (q : Family Mid Output) : Family Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose (p : Family Input Mid) (q : Family Mid Output)
    (inputs : Input → ℂ) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family Input Mid) (q : Family Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

def mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family Input Output) :
    Family NewInput Output :=
  ⟨p.registers, p.program.mapInput f, p.output⟩

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) (inputs : NewInput → ℂ) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

def parallel : (r : ℕ) → (Fin r → Family Input Output) → Family Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        (Program.oldIndex _ _ (head.output o.2))
        (fun i => Program.newIndex _ _ (tail.output (i, o.2))) o.1 }

theorem eval_parallel (r : ℕ) (p : Fin r → Family Input Output)
    (inputs : Input → ℂ) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

theorem cost_parallel (r : ℕ) (p : Fin r → Family Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

def copies (r : ℕ) (p : Family Input Output) :
    Family (Fin r × Input) (Fin r × Output) :=
  parallel r (fun i => p.mapInputs (fun x => (i, x)))

theorem eval_copies (r : ℕ) (p : Family Input Output)
    (inputs : Fin r × Input → ℂ) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

theorem cost_copies (r : ℕ) (p : Family Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

def ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    Family (MatrixInput m) (Fin m × Fin m) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

@[simp] theorem cost_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    (ofMatrix p).cost = p.cost := rfl

theorem eval_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) (hp : p.Correct)
    (inputs : MatrixInput m → ℂ) (o : Fin m × Fin m) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n r m : ℕ}

def join (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

theorem rank_bilinear_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left right : Fin n × Fin n → ℂ) (i k : Fin n) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  change _ = Tensor.contract (Tensor.matrixMultiplication n n n) left right (k, i)
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ =
        ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

def leftBlock (a : Fin r → Fin n × Fin n → ℂ)
    (A : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n × Fin n → ℂ)
    (B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

theorem block_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ)
    (i k : Fin n) (s u : Fin m) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

section BlockPrograms

variable {n r m : ℕ}

def inputExpressions (a b : Fin r → Fin n × Fin n → ℂ) :
    Fin r × MatrixInput m → Expression (MatrixInput (n * m))
  | (q, .inl (s, t)) => LinearExpression.linear (a q)
      (fun x => .inl (join x.1 s, join x.2 t))
  | (q, .inr (t, u)) => LinearExpression.linear (b q)
      (fun y => .inr (join y.1 t, join y.2 u))

def inputFamily (a b : Fin r → Fin n × Fin n → ℂ) :
    Family (MatrixInput (n * m)) (Fin r × MatrixInput m) :=
  Family.expressions (inputExpressions a b)

theorem inputFamily_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (x : MatrixInput m) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a b : Fin r → Fin n × Fin n → ℂ) :
    (inputFamily (m := m) a b).cost = 4 * r * n ^ 2 * m ^ 2 := by
  rw [inputFamily, Family.cost_expressions]
  have hc (o : Fin r × MatrixInput m) : (inputExpressions a b o).cost = 2 * n ^ 2 := by
    rcases o with ⟨q, o⟩
    cases o <;> simp [inputExpressions, LinearExpression.cost_linear, pow_two]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_sum, smul_eq_mul]
  ring

def recursiveProducts (a b : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    Family (MatrixInput (n * m)) (Fin r × (Fin m × Fin m)) :=
  (inputFamily a b).compose (Family.copies r (Family.ofMatrix p))

theorem recursiveProducts_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) (hp : p.Correct)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (s u : Fin m) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (recursiveProducts a b p).cost = 4 * r * n ^ 2 * m ^ 2 + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

def outputExpressions (c : Fin r → Fin n × Fin n → ℂ) :
    Fin (n * m) × Fin (n * m) → Expression (Fin r × (Fin m × Fin m)) :=
  fun o => LinearExpression.linear
    (fun q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

def outputFamily (c : Fin r → Fin n × Fin n → ℂ) :
    Family (Fin r × (Fin m × Fin m)) (Fin (n * m) × Fin (n * m)) :=
  Family.expressions (outputExpressions c)

theorem outputFamily_eval (c : Fin r → Fin n × Fin n → ℂ)
    (inputs : Fin r × (Fin m × Fin m) → ℂ) (i k : Fin n) (s u : Fin m) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n × Fin n → ℂ) :
    (outputFamily (m := m) c).cost = 2 * r * n ^ 2 * m ^ 2 := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

def algorithm (a b c : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    MatrixAlgorithm (n * m) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

theorem algorithm_correct
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm m) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a b c : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (algorithm a b c p).cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step (h : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) r)
    (p : MatrixAlgorithm m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm (n * m), q.Correct ∧
      q.cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end BlockPrograms

end MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

end

end OAI

end FlattenModule010
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.RecursiveBlockPrograms -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth -/
section FlattenModule011








namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C]; linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C]; linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add_right hmul _
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C]; linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

theorem power_cost_padding_bound
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ s) ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  refine ⟨C * (b : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hbpos s), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hcost⟩ := hpower k
  obtain ⟨Q, hQ, hQP⟩ := hpad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((b : ℝ) ^ s) ^ k := hcost
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hC.le
    _ = (C * (b : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]
      ring

theorem admissibleExponent_of_uniform_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ τ) ^ k) :
    AdmissibleExponent τ := by
  obtain ⟨D, hD, hall⟩ := power_cost_padding_bound hpad hb hτ hC hpower
  intro ε hε
  refine ⟨D, hD, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hall n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hD.le

theorem admissibleExponent_of_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ (τ + ε)) ^ k) :
    AdmissibleExponent τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact power_cost_padding_bound hpad hb (by linarith) hC hcost

theorem admissibleExponent_of_recursive_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (P : ∀ k : ℕ, MatrixAlgorithm (b ^ k))
    (hP : ∀ k, (P k).Correct)
    (hstep : ∀ k, (P (k + 1)).cost ≤ R * (P k).cost + K * (b ^ k) ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => ((P k).cost : ℝ)) (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ))
    ((b : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (sq_nonneg _) hrate hquad (fun k => by
      have h := hstep k
      have hcast : ((P (k + 1)).cost : ℝ) ≤
          (R : ℝ) * ((P k).cost : ℝ) + (K : ℝ) * ((b : ℝ) ^ k) ^ 2 := by
        exact_mod_cast h
      simpa only [← pow_mul, Nat.mul_comm k 2] using hcast)
  exact ⟨C, hC, fun k => ⟨P k, hP k, hbound k⟩⟩

def blockRecurrenceCost (b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2

@[simp] theorem blockRecurrenceCost_zero (b R K : ℕ) :
    blockRecurrenceCost b R K 0 = 1 := rfl

@[simp] theorem blockRecurrenceCost_succ (b R K k : ℕ) :
    blockRecurrenceCost b R K (k + 1) =
      R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2 := rfl

theorem power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k), P.Correct ∧
      P.cost ≤ blockRecurrenceCost b R K k := by
  intro k
  induction k with
  | zero =>
    exact ⟨scalarAlgorithm, scalarAlgorithm_correct, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    have hbound : Q.cost ≤ blockRecurrenceCost b R K (k + 1) := by
      exact hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)
    have hresult : ∃ Q : MatrixAlgorithm (b * b ^ k), Q.Correct ∧
        Q.cost ≤ blockRecurrenceCost b R K (k + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' b k).symm ▸ hresult

theorem admissibleExponent_of_block_step_of_padding
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost b R K k : ℝ))
    (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ)) ((b : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  refine ⟨C, hC, ?_⟩
  intro k
  obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (blockRecurrenceCost b R K k : ℝ)).trans (hbound k)⟩

theorem admissibleExponent_of_block_step
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ :=
  admissibleExponent_of_block_step_of_padding
    (fun h P hP => MatrixAlgorithm.exists_restrict h P hP) hb hτ hR hstep

theorem admissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_block_step (K := 6 * R * n ^ 2) hn hτ hR
  intro m P hP
  obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
  exact ⟨Q, hQ, hcost.le⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule011
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth -/



/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity -/
section FlattenModule013



namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {F Input Register : Type*}

end Gate

namespace Program

variable {F Input : Type*}

@[simp] theorem eval_step_zero [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm (F : Type*) [Field F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost (F : Type*) [Field F] : (scalarAlgorithm F).cost = 1 := rfl

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

theorem innerSize_mono {n : ℕ} (hn : 1 ≤ n) {k l : ℝ} (hkl : k ≤ l) :
    innerSize n k ≤ innerSize n l := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hkl)

theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

theorem innerSize_cast_le {n : ℕ} (hn : 1 ≤ n) {k : ℝ} (hk : 0 ≤ k) :
    (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  have hpow : 1 ≤ (n : ℝ) ^ k := Real.one_le_rpow (by exact_mod_cast hn) hk
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) k)).le
  change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
  linarith

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule013
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm -/
section FlattenModule014


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression Input) → Expression Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {n : ℕ} (i k : Fin n) : Expression (MatrixInput n) :=
  Expression.sumFin fun j : Fin n =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {n : ℕ} (i k : Fin n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {n : ℕ} (i k : Fin n) :
    (naiveEntry i k).cost = 2 * n := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (n : ℕ) : MatrixAlgorithm n :=
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (n : ℕ) : (naiveAlgorithm n).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (n : ℕ) : (naiveAlgorithm n).cost = 2 * n ^ 3 := by
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (n : ℕ) : (naiveAlgorithm n).cost ≤ 2 * n ^ 3 :=
  (naiveAlgorithm_cost n).le

theorem admissibleExponent_three : AdmissibleExponent 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n, naiveAlgorithm_correct n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule014
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound -/
section FlattenModule015



namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Program

theorem eval_eq_constant_or_input_of_cost_eq_zero {Input : Type*} {r : ℕ}
    (p : Program Input r) (hp : p.cost = 0) (i : Fin r) :
    (∃ z : ℂ, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert hp i
  induction p with
  | nil =>
    intro _ i
    exact Fin.elim0 i
  | @step r p g ih =>
    intro hp i
    have hcost : p.cost + g.cost = 0 := hp
    have hp0 : p.cost = 0 := by omega
    have hg0 : g.cost = 0 := by omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hg0
      | sub a b => simp [Gate.cost] at hg0
      | mul a b => simp [Gate.cost] at hg0
    · simpa only [eval_step_succ] using ih hp0 j

end Program

namespace MatrixAlgorithm

theorem one_le_cost {n : ℕ} (P : MatrixAlgorithm n) (hn : 1 ≤ n)
    (hP : P.Correct) : 1 ≤ P.cost := by
  by_contra hcost
  have hzero : P.program.cost = 0 := by
    change ¬ 1 ≤ P.program.cost at hcost
    omega
  let i : Fin n := ⟨0, by omega⟩
  have hentry (A B : Matrix (Fin n) (Fin n) ℂ) :
      P.program.eval (matrixInputs A B) (P.output i i) = (A * B) i i :=
    congrFun (congrFun (hP A B) i) i
  rcases P.program.eval_eq_constant_or_input_of_cost_eq_zero hzero (P.output i i)
      with ⟨z, hz⟩ | ⟨a, ha⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry 1 1
      rw [hz] at h
      simpa using h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (hz0.symm.trans hz1)
  · rcases a with ⟨j, k⟩ | ⟨j, k⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h

end MatrixAlgorithm

theorem admissibleExponent_nonneg {τ : ℝ} (hτ : AdmissibleExponent τ) : 0 ≤ τ := by
  by_contra hneg
  have hτneg : τ < 0 := lt_of_not_ge hneg
  let ε : ℝ := -τ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum : τ + ε = -ε := by dsimp [ε]; ring
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hcostone : (1 : ℝ) ≤ P.cost :=
    (Nat.one_le_cast (α := ℝ)).mpr (P.one_le_cost hn1 hP)
  rw [hsum, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv] at hcost
  have hsmall : C / (n : ℝ) ^ ε < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hnpos ε)).mpr hpow
  exact (not_lt_of_ge (hcostone.trans hcost)) hsmall

theorem admissibleExponent_bddBelow : BddBelow {τ : ℝ | AdmissibleExponent τ} := by
  refine ⟨0, ?_⟩
  intro τ hτ
  exact admissibleExponent_nonneg hτ

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule015
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent -/
section FlattenModule016


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_le_of_admissibleExponent {τ : ℝ} (hτ : AdmissibleExponent τ) :
    omega ≤ τ :=
  csInf_le admissibleExponent_bddBelow hτ

theorem omega_nonneg : 0 ≤ omega :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_nonneg hτ)

theorem omega_le_three : omega ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent omega := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent σ} < omega + ε / 2 from
      lt_add_of_pos_right omega hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent τ ↔ omega ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule016
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility -/
section FlattenModule017


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {Input Register : Type*}

def toLegacy : Gate ℂ Input Register → MatrixMultiplication.Foundation.Arithmetic.Gate Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

def ofLegacy : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register → Gate ℂ Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_toLegacy (g : Gate ℂ Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    g.toLegacy.eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_toLegacy (g : Gate ℂ Input Register) : g.toLegacy.cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    (ofLegacy g).eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register) :
    (ofLegacy g).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def toLegacy : {r : ℕ} → Program ℂ Input r → MatrixMultiplication.Foundation.Arithmetic.Program Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => p.toLegacy.step g.toLegacy

def ofLegacy : {r : ℕ} → MatrixMultiplication.Foundation.Arithmetic.Program Input r → Program ℂ Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => (ofLegacy p).step (Gate.ofLegacy g)

@[simp] theorem eval_toLegacy {r : ℕ} (p : Program ℂ Input r) (inputs : Input → ℂ) :
    p.toLegacy.eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_toLegacy, ih]
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_toLegacy {r : ℕ} (p : Program ℂ Input r) : p.toLegacy.cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_toLegacy, ih]

@[simp] theorem eval_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) (inputs : Input → ℂ) :
    (ofLegacy p).eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_ofLegacy, ih]
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) : (ofLegacy p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_ofLegacy, ih]

end Program

namespace MatrixAlgorithm

def toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n :=
  ⟨P.registers, P.program.toLegacy, P.output⟩

def ofLegacy {n : ℕ} (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    MatrixAlgorithm ℂ n n n :=
  ⟨P.registers, Program.ofLegacy P.program, P.output⟩

@[simp] theorem eval_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : P.toLegacy.eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change P.program.toLegacy.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B)
    (P.output i k) = P.program.eval (matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (P.program.eval_toLegacy (matrixInputs A B)) (P.output i k)

@[simp] theorem eval_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (ofLegacy P).eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change (Program.ofLegacy P.program).eval (matrixInputs A B) (P.output i k) =
    P.program.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (Program.eval_ofLegacy P.program (matrixInputs A B)) (P.output i k)

theorem toLegacy_correct {n : ℕ} {P : MatrixAlgorithm ℂ n n n}
    (hP : P.Correct) : P.toLegacy.Correct := by
  intro A B
  exact (P.eval_toLegacy A B).trans (hP A B)

theorem ofLegacy_correct {n : ℕ} {P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n}
    (hP : P.Correct) : (ofLegacy P).Correct := by
  intro A B
  exact (eval_ofLegacy P A B).trans (hP A B)

@[simp] theorem cost_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    P.toLegacy.cost = P.cost := P.program.cost_toLegacy

@[simp] theorem cost_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    (ofLegacy P).cost = P.cost := Program.cost_ofLegacy P.program

end MatrixAlgorithm

theorem complex_admissibleExponent_iff (τ : ℝ) :
    AdmissibleExponent ℂ τ ↔ MatrixMultiplication.Foundation.Arithmetic.AdmissibleExponent τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨P.toLegacy, MatrixAlgorithm.toLegacy_correct hP, by simpa using hcost⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨MatrixAlgorithm.ofLegacy P, MatrixAlgorithm.ofLegacy_correct hP,
      by simpa using hcost⟩

theorem complex_omega_eq : omega ℂ = MatrixMultiplication.Foundation.Arithmetic.omega := by
  unfold omega MatrixMultiplication.Foundation.Arithmetic.omega
  congr 1
  ext τ
  exact complex_admissibleExponent_iff τ

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule017
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs -/
section FlattenModule018


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate F Input R → Gate F Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate F Input R) (f : R → S)
    (inputs : Input → F) (registers : S → F) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapRegister (g : Gate F Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program F Input r) : {s : ℕ} → Program F Input s → Program F Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

omit [Field F] in
@[simp] theorem cost_append {r s : ℕ} (p : Program F Input r) (q : Program F Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (F Input : Type*) where
  | constant : F → Expression F Input
  | input : Input → Expression F Input
  | add : Expression F Input → Expression F Input → Expression F Input
  | sub : Expression F Input → Expression F Input → Expression F Input
  | mul : Expression F Input → Expression F Input → Expression F Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → F) : Expression F Input → F
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression F Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression F Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule018
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily -/
section FlattenModule019



namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.Expression

variable {F : Type*} [Field F]

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression F Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression F Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Arithmetic.Expression

end

end OAI

end FlattenModule019
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm -/
section FlattenModule020


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost ≤ 2 * a * b * c :=
  (naiveAlgorithm_cost a b c).le

theorem admissibleExponent_three : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_correct n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule020
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound -/
section FlattenModule021




namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε]; ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

theorem admissibleExponent_iff_rectangular_one (F : Type*) [Field F] (τ : ℝ) :
    AdmissibleExponent F τ ↔ RectangularAdmissibleExponent F 1 τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [innerSize_one]
    exact hbound n hn
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hnBound := hbound n hn
    rw [innerSize_one] at hnBound
    exact hnBound

theorem admissibleExponent_two_le {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ :=
  rectangularAdmissibleExponent_two_le ((admissibleExponent_iff_rectangular_one F τ).mp hτ)

theorem admissibleExponent_bddBelow (F : Type*) [Field F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩

theorem omega_le_of_admissibleExponent {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : omega F ≤ τ :=
  csInf_le (admissibleExponent_bddBelow F) hτ

@[simp] theorem rectangularOmega_one (F : Type*) [Field F] :
    rectangularOmega F 1 = omega F := by
  unfold rectangularOmega omega
  congr 1
  ext τ
  exact (admissibleExponent_iff_rectangular_one F τ).symm

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule021
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition -/
section FlattenModule022

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate F Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ F) : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r)
    (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ F) : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program F Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program F Input r} {q : Program F Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate F Mid (Fin s)) (h : Gate F Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule022
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding -/
section FlattenModule023

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

def zeroPadMatrix {a b : ℕ} (A B : ℕ) (M : Matrix (Fin a) (Fin b) F) :
    Matrix (Fin A) (Fin B) F :=
  fun i j => if hi : i.val < a then
    if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (M : Matrix (Fin a) (Fin b) F) (i : Fin a) (j : Fin b) :
    zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) = M i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → F)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin B,
        zeroPadMatrix A B M (Fin.castLE ha i) j *
          zeroPadMatrix B C N j (Fin.castLE hc k)) =
        ∑ j : Fin b,
          zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
            zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k) := by
      apply sum_fin_castLE_of_zero hb
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin b, M i j * N j k := by simp

def padSource {a b c A B C : ℕ} : MatrixInput A B C → MatrixInput a b c ⊕ F
  | .inl (i, j) => if hi : i.val < a then
      if hj : j.val < b then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (j, k) => if hj : j.val < b then
      if hk : k.val < c then .inl (.inr (⟨j.val, hj⟩, ⟨k.val, hk⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk]

namespace MatrixAlgorithm

def pad {a b c A B C : ℕ} (ha : a ≤ A) (_hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : MatrixAlgorithm F a b c where
  registers := P.registers
  program := P.program.mapSource (padSource (a := a) (b := b) (c := c))
  output := fun i k => P.output (Fin.castLE ha i) (Fin.castLE hc k)

theorem pad_correct {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : P.Correct) : (pad ha hb hc P).Correct := by
  intro M N
  funext i k
  change (P.program.mapSource (padSource (a := a) (b := b) (c := c))).eval
    (matrixInputs M N) (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = (M * N) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N)) (Fin.castLE ha i)) (Fin.castLE hc k)
  exact hentry.trans (zeroPadMatrix_mul ha hb hc M N i k)

@[simp] theorem pad_cost_eq {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : (pad ha hb hc P).cost = P.cost :=
  Program.cost_mapSource (padSource (a := a) (b := b) (c := c)) P.program

theorem exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad ha hb hc P, pad_correct ha hb hc hP, (pad_cost_eq ha hb hc P).le⟩

end MatrixAlgorithm

theorem RectangularAdmissibleExponent.mono_aspect {k l τ : ℝ}
    (h : RectangularAdmissibleExponent F l τ) (hkl : k ≤ l) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  obtain ⟨Q, hQ, hcostQ⟩ := MatrixAlgorithm.exists_restrict (le_refl n)
    (innerSize_mono hn hkl) (le_refl n) P hP
  exact ⟨Q, hQ, (Nat.cast_le.mpr hcostQ).trans hcost⟩

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule023
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent -/
section FlattenModule024



namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent F τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent F σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_two_le : 2 ≤ omega F :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_two_le hτ)

theorem omega_nonneg : 0 ≤ omega F := le_trans (by norm_num) omega_two_le

theorem omega_le_three : omega F ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent F (omega F) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent F σ} < omega F + ε / 2 from
      lt_add_of_pos_right (omega F) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent F τ ↔ omega F ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

theorem RectangularAdmissibleExponent.mono {k τ σ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) (hτσ : τ ≤ σ) :
    RectangularAdmissibleExponent F k σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

theorem rectangularOmega_admissibleExponent (k : ℝ) :
    RectangularAdmissibleExponent F k (rectangularOmega F k) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt (rectangularAdmissibleExponent_nonempty k)
    (show sInf {σ : ℝ | RectangularAdmissibleExponent F k σ} <
        rectangularOmega F k + ε / 2 from lt_add_of_pos_right (rectangularOmega F k) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem rectangularAdmissibleExponent_iff_omega_le {k τ : ℝ} :
    RectangularAdmissibleExponent F k τ ↔ rectangularOmega F k ≤ τ :=
  ⟨rectangularOmega_le_of_admissibleExponent, (rectangularOmega_admissibleExponent k).mono⟩

theorem rectangularOmega_mono {k l : ℝ} (hkl : k ≤ l) :
    rectangularOmega F k ≤ rectangularOmega F l :=
  rectangularOmega_le_of_admissibleExponent
    ((rectangularOmega_admissibleExponent l).mono_aspect hkl)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

theorem complexAlpha_set_nonempty :
    Set.Nonempty {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨0, ⟨by norm_num, by norm_num⟩, rectangularOmega_zero⟩

theorem complexAlpha_set_bddAbove :
    BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨1, fun _ h => h.1.2⟩

theorem le_complexAlpha {k : ℝ} (hk : k ∈ Set.Icc 0 1)
    (hω : rectangularOmega ℂ k = 2) : k ≤ complexAlpha :=
  le_csSup complexAlpha_set_bddAbove ⟨hk, hω⟩

theorem complexAlpha_le_one : complexAlpha ≤ 1 :=
  csSup_le complexAlpha_set_nonempty (fun _ h => h.1.2)

theorem complexAlpha_nonneg : 0 ≤ complexAlpha :=
  le_complexAlpha ⟨le_refl 0, by norm_num⟩ rectangularOmega_zero

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule024
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent -/
section FlattenModule025




namespace OAI

/-!
# From exact tensor rank to arithmetic complexity

This file supplies the arithmetic conversion in Section 6.2.  It uses the
existing division-free straight-line programs over `ℂ`: loading inputs and
constants is free, and each scalar addition, subtraction, or multiplication
costs one.  Correctness means matrix multiplication on every pair of inputs.

The substantive tensor estimates are separate.  Here `omega` is an alias for
the existing arithmetic exponent, and the general bridge proves
`omega ≤ exactRankExponent`.  Thus any independently established upper bound
on the exact-rank exponent gives an arithmetic bound with every positive
exponent slack.  No particular numerical upper bound is assumed or asserted.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The arithmetic matrix multiplication exponent over the complex numbers,
in the repository's existing scalar-operation model. -/
abbrev omega : ℝ := MatrixMultiplication.Arithmetic.omega ℂ

/-- A uniform scalar-operation bound with arbitrary positive exponent slack. -/
abbrev ArithmeticBound (τ : ℝ) : Prop :=
  MatrixMultiplication.Arithmetic.AdmissibleExponent ℂ τ

/-- The existing arithmetic exponent is itself admissible; hence its infimum
has exactly the expected upper-bound interpretation. -/
theorem arithmeticBound_iff_omega_le {τ : ℝ} :
    ArithmeticBound τ ↔ omega ≤ τ :=
  MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le

/-- Expanded form of the arithmetic statement, including its quantifier order
and the correctness and operation cost of the resulting programs. -/
theorem arithmeticComplexity_iff_omega_le {τ : ℝ} :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
          P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)) ↔ omega ≤ τ :=
  arithmeticBound_iff_omega_le

/-- A finite exact decomposition gives an arithmetic bound by block
substitution, including all the scalar operations in the linear combinations,
followed by padding to arbitrary positive sizes. -/
theorem arithmeticBound_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    ArithmeticBound τ :=
  (MatrixMultiplication.Arithmetic.complex_admissibleExponent_iff τ).mpr
    (MatrixMultiplication.Foundation.Arithmetic.admissibleExponent_of_rankAtMost hn hRank hτ hR)

theorem omega_le_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    omega ≤ τ :=
  arithmeticBound_iff_omega_le.mp (arithmeticBound_of_rankAtMost hn hRank hτ hR)

/-- The quadratic rank lower bound pays for the quadratic block-combination
overhead, including the boundary case of rank exactly `n²`. -/
theorem omega_le_logb_rank {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R) :
    omega ≤ Real.logb (n : ℝ) (R : ℝ) := by
  have hquad : n ^ 2 ≤ R := matrixMultiplication_rank_lower (by omega) hRank
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hR0 : 0 < (R : ℝ) := by
    have : 0 < n ^ 2 := pow_pos (by omega : 0 < n) _
    exact_mod_cast (this.trans_le hquad)
  have hτ : 2 ≤ Real.logb (n : ℝ) (R : ℝ) := by
    apply (Real.le_logb_iff_rpow_le hn1 hR0).mpr
    simpa only [Real.rpow_two, Nat.cast_pow] using
      (Nat.cast_le.mpr hquad : ((n ^ 2 : ℕ) : ℝ) ≤ (R : ℝ))
  exact omega_le_of_rankAtMost hn hRank hτ
    (Real.rpow_logb hn0 (ne_of_gt hn1) hR0).symm.le

/-- Near-optimal finite blocks suffice: no finite decomposition is required
to attain the limiting exponent. -/
theorem arithmeticBound_of_arbitrarily_close_rankBounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ δ : ℝ, 0 < δ → ∃ n R : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R ∧
        (R : ℝ) ≤ (n : ℝ) ^ (τ + δ)) : ArithmeticBound τ := by
  apply arithmeticBound_iff_omega_le.mpr
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, R, hn, hRank, hR⟩ := hRank δ hδ
  exact omega_le_of_rankAtMost hn hRank (by linarith) hR

/-- The arithmetic exponent is bounded by each exact finite-block exponent. -/
theorem omega_le_exactMatrixRank_logb {n : ℕ} (hn : 2 ≤ n) :
    omega ≤ Real.logb (n : ℝ) (exactMatrixRank n : ℝ) :=
  omega_le_logb_rank hn (exactMatrixRank_spec n)

/-- General exact-rank-to-arithmetic bridge.  The proof uses a lower bound for
every finite-block exponent, so it does not require attainment of the infimum. -/
theorem omega_le_exactRankExponent : omega ≤ exactRankExponent := by
  apply le_csInf exactRankExponentSet_nonempty
  rintro τ ⟨n, hn, rfl⟩
  exact omega_le_exactMatrixRank_logb hn

theorem arithmeticBound_exactRankExponent : ArithmeticBound exactRankExponent :=
  arithmeticBound_iff_omega_le.mpr omega_le_exactRankExponent

/-- Any upper bound on the exact-rank exponent gives the same arithmetic
exponent bound, with arbitrary positive slack. -/
theorem arithmeticBound_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) : ArithmeticBound τ :=
  arithmeticBound_iff_omega_le.mpr (omega_le_exactRankExponent.trans hτ)

/-- Explicit epsilon-complexity conclusion from an exact-rank exponent bound. -/
theorem arithmeticComplexity_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε) :=
  arithmeticBound_of_exactRankExponent_le hτ ε hε

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule025
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent -/



noncomputable section
open scoped BigOperators
open PiTensorProduct

namespace MMECircuitBridge

def coordinate {n : ℕ} (x y z : Fin n × Fin n) (i : Fin 3) :
    MME.MMSpace ℂ n n n i →ₗ[ℂ] ℂ :=
  match i with
  | ⟨0, _⟩ => LinearMap.proj x
  | ⟨1, _⟩ => LinearMap.proj y
  | ⟨2, _⟩ => LinearMap.proj z

def coefficient {n : ℕ} (x y z : Fin n × Fin n) :
    PiTensorProduct ℂ (MME.MMSpace ℂ n n n) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compLinearMap (coordinate x y z))

@[simp] theorem coefficient_tprod {n : ℕ} (x y z : Fin n × Fin n)
    (f : ∀ i, MME.MMSpace ℂ n n n i) :
    coefficient x y z (tprod ℂ f) = f 0 x * f 1 y * f 2 z := by
  simp [coefficient, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_succ, coordinate, mul_assoc]

@[simp] theorem coefficient_matrix {n : ℕ} (x y z : Fin n × Fin n) :
    coefficient x y z (MME.MMTensor ℂ n n n) =
      if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 := by
  classical
  simp [MME.MMTensor, coefficient_tprod, Pi.single_apply, Prod.ext_iff,
    ite_and, mul_ite]
  split_ifs <;> simp_all

theorem matrix_decomposition_exists (n : ℕ) :
    ∃ r : ℕ, ∃ f : Fin r → ∀ i, MME.MMSpace ℂ n n n i,
      MME.MMTensor ℂ n n n = ∑ j, tprod ℂ (f j) := by
  classical
  let f (p : Fin n × Fin n × Fin n) (s : Fin 3) : MME.MMSpace ℂ n n n s :=
    match s with
    | ⟨0, _⟩ => Pi.single (p.1, p.2.1) 1
    | ⟨1, _⟩ => Pi.single (p.2.1, p.2.2) 1
    | ⟨2, _⟩ => Pi.single (p.2.2, p.1) 1
  refine ⟨Fintype.card (Fin n × Fin n × Fin n),
    fun j => f ((Fintype.equivFin _).symm j), ?_⟩
  calc
    MME.MMTensor ℂ n n n = ∑ p, tprod ℂ (f p) := by
      simp [MME.MMTensor, f, Fintype.sum_prod_type]
      rfl
    _ = _ := (Equiv.sum_comp
      (Fintype.equivFin (Fin n × Fin n × Fin n)).symm
      (fun p => tprod ℂ (f p))).symm

theorem matrix_rank_decomposition (n : ℕ) :
    ∃ f : Fin (MME.tensorRank (MME.MMTensor ℂ n n n)) →
        ∀ i, MME.MMSpace ℂ n n n i,
      MME.MMTensor ℂ n n n = ∑ j, tprod ℂ (f j) :=
  Nat.sInf_mem (matrix_decomposition_exists n)

end MMECircuitBridge

noncomputable section
open scoped BigOperators
open OAI.MatrixMultiplication

namespace MMECircuitBridge

theorem coefficient_rankAtMost (n : ℕ) :
    Foundation.Tensor.RankAtMost (Foundation.Tensor.matrixMultiplication n n n)
      (MME.tensorRank (MME.MMTensor ℂ n n n)) := by
  obtain ⟨f, hf⟩ := matrix_rank_decomposition n
  refine ⟨fun j => f j 0, fun j => f j 1, fun j => f j 2, ?_⟩
  funext x y z
  have h := congrArg (coefficient x y z) hf
  simpa [Foundation.Tensor.matrixMultiplication, Foundation.Tensor.rankOne] using h

end MMECircuitBridge

/-- Every upper bound from the tensor-rank campaign is an upper bound for
the published arithmetic-circuit exponent over the complex numbers. -/
theorem solution : Arithmetic.omega ℂ ≤ MME.matMulExp ℂ := by
  unfold MME.matMulExp
  apply le_ciInf
  intro n
  split_ifs with hn
  · simpa [Real.logb] using
      AuxiliarySeparation.omega_le_logb_rank (by omega : 2 ≤ n)
        (MMECircuitBridge.coefficient_rankAtMost n)
  · exact Arithmetic.omega_le_three

#print axioms solution
